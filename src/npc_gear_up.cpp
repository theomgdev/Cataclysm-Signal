#include "activity_actor_definitions.h"

#include <algorithm>
#include <array>
#include <climits>
#include <cmath>
#include <functional>
#include <limits>
#include <list>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#include "activity_handlers.h"
#include "activity_item_handling.h"
#include "avatar.h"
#include "body_part_set.h"
#include "bodypart.h"
#include "calendar.h"
#include "character.h"
#include "character_attire.h"
#include "character_id.h"
#include "character_modifier.h"
#include "clzones.h"
#include "coordinates.h"
#include "creature.h"
#include "damage.h"
#include "debug.h"
#include "enums.h"
#include "faction.h"
#include "flag.h"
#include "game.h"
#include "game_constants.h"
#include "item.h"
#include "item_category.h"
#include "item_location.h"
#include "item_pocket.h"
#include "itype.h"
#include "line.h"
#include "map.h"
#include "map_selector.h"
#include "messages.h"
#include "npc.h"
#include "npc_gear_up.h"
#include "npctalk.h"
#include "output.h"
#include "player_activity.h"
#include "ret_val.h"
#include "translations.h"
#include "units.h"
#include "value_ptr.h"
#include "vehicle.h"
#include "vehicle_selector.h"
#include "visitable.h"
#include "vpart_position.h"
#include "weather.h"
#include "weather_type.h"

/*
 * "Gear up from the stores": the character walks the faction's loot and camp
 * zones tile by tile, the way loot sorting does, and equips from what is
 * stored there, containers included.  Displaced gear goes back to the zone the
 * zone manager picks for it.  NPCs are given the order in conversation, the
 * avatar takes it from the zone-activities menu.
 *
 * Equipment first (weapon, backup blade, clothing, plates for a carrier),
 * supplies second (magazines, ammunition, medical, rations, water).  The stage
 * advances only once no tile offers an equipment improvement, so the weapon is
 * settled before ammunition is chosen for it.  Within clothing, pockets come
 * first while there are none: everything the supply stage does needs somewhere
 * to put what it picks up.
 *
 * Clothing is judged as a whole outfit rather than piece by piece: protection
 * that saturates, bare skin, weather and pockets on one side, and on the other
 * what the encumbrance costs, read off the engine's own limb scores.  A change
 * is made only when it improves that balance, and the same balance decides
 * which worn pieces cost more than they protect and come off.
 *
 * Termination hinges on gear_up_rejected: types tried and turned down, or that
 * could not be carried, are remembered.  The engine's loop detector cannot see
 * a character circling back to the same crate, because every lap spends moves.
 */

static const character_modifier_id character_modifier_limb_dodge_mod( "limb_dodge_mod" );
static const character_modifier_id character_modifier_limb_run_cost_mod( "limb_run_cost_mod" );
static const character_modifier_id
character_modifier_melee_attack_roll_mod( "melee_attack_roll_mod" );
static const character_modifier_id
character_modifier_melee_thrown_move_balance_mod( "melee_thrown_move_balance_mod" );
static const character_modifier_id character_modifier_reloading_move_mod( "reloading_move_mod" );
static const character_modifier_id
character_modifier_stamina_recovery_breathing_mod( "stamina_recovery_breathing_mod" );

static const damage_type_id damage_bash( "bash" );
static const damage_type_id damage_bullet( "bullet" );
static const damage_type_id damage_cut( "cut" );
static const damage_type_id damage_stab( "stab" );

static const efftype_id effect_mending( "mending" );

static const item_category_id item_category_weapons( "weapons" );

static const itype_id itype_acetaminophen( "acetaminophen" );
static const itype_id itype_aspirin( "aspirin" );
static const itype_id itype_codeine( "codeine" );
static const itype_id itype_heroin( "heroin" );
static const itype_id itype_ibuprofen( "ibuprofen" );
static const itype_id itype_oxycodone( "oxycodone" );
static const itype_id itype_tramadol( "tramadol" );

static const limb_score_id limb_score_block( "block" );
static const limb_score_id limb_score_grip( "grip" );
static const limb_score_id limb_score_reaction( "reaction" );
static const limb_score_id limb_score_vision( "vision" );

static const zone_type_id zone_type_CAMP_FOOD( "CAMP_FOOD" );
static const zone_type_id zone_type_CAMP_STORAGE( "CAMP_STORAGE" );
static const zone_type_id zone_type_LOOT_IGNORE( "LOOT_IGNORE" );
static const zone_type_id zone_type_LOOT_UNSORTED( "LOOT_UNSORTED" );
static const zone_type_id zone_type_NO_NPC_PICKUP( "NO_NPC_PICKUP" );

namespace
{

// Bumped by reset_gear_up_caches() to invalidate every (turn, character)
// cache below out of band.  In real play calendar::turn only ever advances,
// so a (turn, character) key alone is safe; a test process reuses the same
// avatar object and resets calendar::turn to the same constant for every
// TEST_CASE, which without this would let a scan cached by one test answer
// for a completely different scenario in the next one.
unsigned int gear_up_cache_generation = 0;

// What "enough supplies for a fight" means, in numbers, so that falling short
// of it is something the code can act on.
constexpr int want_healing_items = 3;
constexpr int want_painkillers = 4;
constexpr int want_kcal = 2400;
constexpr int want_quench = 400;
constexpr int want_ammo_loads = 3;
constexpr int want_spare_magazines = 2;
constexpr int want_drink_vessels = 2;

// A throwing stock is what buys the seconds between the magazine running dry
// and the blade coming out, so it is budgeted by what it costs to carry
// rather than by a count: a pocketful of rocks and a single javelin both fill
// it.  Past this a character is hauling a quarry around for a tactic they use
// once a fight.  A rock weighs 657 g, so the weight budget is what decides how
// many of them a character leaves with; it is set to carry a stack of eight
// rather than the three a tighter budget allows, since a character walking out
// of the camp has the capacity to spare and runs out of throwables long before
// it runs out of pockets.
constexpr units::volume want_thrown_volume = 5_liter;
constexpr units::mass want_thrown_weight = 6250_gram;
// One stack should not eat the whole budget on its own, so that a crate of
// darts still leaves room for nothing else to be wrong.
constexpr int want_thrown_per_stack = 8;

// Carrying capacity worth having: ammunition, a medical kit, a day of food
// and water, some salvage.  Past that a liter of pocket keeps a tenth of its
// credit, or storage outscores real armour once a character has a bag or two.
constexpr double want_storage_liters = 25.0;
constexpr double weight_storage_per_liter = 0.30;
constexpr double weight_storage_marginal = weight_storage_per_liter * 0.1;

// Below this, a bag or a pair of pockets is sought to the exclusion of
// everything else armour has to offer.  Storage is a prerequisite, not one
// candidate competing on its own merits: can_stash() refuses a backup blade,
// spare ammunition and medical supplies alike without room to put them, so
// deferring pockets to a raw score contest against real armour can starve
// them indefinitely whenever the camp has enough of the latter.
constexpr double want_storage_liters_floor = 3.0;

// The first liters of pocket are not one candidate among many: without them
// nothing else the order does can be carried.  This is the extra credit for
// reaching the floor above, spread evenly over the liters short of it.
constexpr double weight_storage_floor = 30.0;

// What exposure costs.  Bare skin is not a free baseline: cloth that stops
// thorns, sun, weather and scrapes registers as almost no armour at all, so
// judged on resistance alone a plain pair of jeans lands a fraction under
// nothing and the character walks into a fight bare-legged.  Every body part
// is credited for the best coverage standing in front of it.
constexpr double weight_bare_skin = 6.0;
// Bare skin hurts out of all proportion to the blows it takes: glass underfoot,
// frostbitten fingers, a splinter in an eye.  No part is credited for less than
// this share of the body.
constexpr double share_exposure_floor = 0.05;

// Encumbrance is priced by what the engine does with it, not by its number.
// Each body part's encumbrance bends the limb scores that dodging, movement,
// breathing and handling are made of along a hyperbola, so the 70 on a bomb
// suit's torso is a different order of cost from the 7 on a coat's.  What is
// priced is the shortfall in each of those abilities, as the ln of what is
// kept and squared: a tenth lost to a pair of boots is a nuisance, half lost to
// a suit of armour is a collapse, and a coat on top of a pack costs more than
// either alone.  In armour points per unit.
constexpr double weight_efficiency_lost = 150.0;

// Protection is scaled by the share of the body a piece stands in front of,
// which for anything short of a full suit is a small fraction.  This puts the
// result back on the same scale as the storage, warmth and encumbrance terms
// it is added to.
constexpr double weight_hit_share = 6.0;

// Resistance counts in proportion to the hits it meets.  Once a layer stops a
// blow, another on top of it adds little, so each damage type saturates at the
// size of a hit it is measured against.
constexpr size_t hit_kinds = 4;
const std::array<std::pair<damage_type_id, double>, hit_kinds> reference_hits = { {
        { damage_bash, 20.0 }, { damage_cut, 25.0 }, { damage_stab, 25.0 }, { damage_bullet, 40.0 }
    }
};

// Armour is carried all day, and its mass is what the ammunition, food and
// medicine are not carried in.
constexpr double weight_per_kilogram = 1.0;

// A swap or a new garment has to be worth this much, in the same points, to be
// made at all: scores come from floating point, and a gain too small to see is
// how two near-identical pieces trade places forever.  Taking something off for
// nothing in return asks for more, since the replacement at least is a visible
// improvement.
constexpr double margin_garment = 1.0;
constexpr double margin_shed = 5.0;

// Gear carried in the hand -- a briefcase, a bindle -- leaves it unable to
// hold a two-handed weapon, which is worth far more than the pockets while one
// is in hand and still something when one may yet be.
constexpr double weight_hands_taken_armed = 60.0;
constexpr double weight_hands_taken = 15.0;

// Environmental protection this high on the face is a respirator.
constexpr int env_resist_respirator = 10;

// A splint on a limb that is broken and not yet mending is the one piece of
// "armour" that treats the injury.
constexpr double weight_splint = 40.0;

// Warmth is credited only while short of the planning target; past that it
// is a smaller liability, not a bonus.
constexpr double weight_warmth_needed = 0.10;
constexpr double weight_warmth_excess = 0.05;

// Filthy gear risks infection through any wound.  Better than nothing, worse
// than the clean equivalent.
constexpr double filth_penalty = 2.0;

// Dressing for the reading on the thermometer right now is how someone ends up
// freezing after dark.  Plan for a colder moment than the current one.
constexpr int night_margin_c = 8;
// At or above this ambient temperature no extra warmth is wanted at all.
constexpr int comfort_temperature_c = 21;
// Roughly how much clothing warmth one degree of missing ambient heat costs.
constexpr double warmth_per_degree = 4.0;

// Going through a crate costs time whether or not anything comes of it, and
// moving one item in or out of a container costs a little more.
constexpr int search_cost_moves = 30;
constexpr int handle_cost_moves = 20;

// How deep into nested containers to look.  A crate holding a first aid kit
// holding bandages is two; beyond three is packing material, not storage.
constexpr int max_nesting_depth = 3;

enum class gear_stage : int {
    equipment = 0,
    supplies = 1,
};

// ---------------------------------------------------------------------------
// Small predicates
// ---------------------------------------------------------------------------

bool is_painkiller( const item &it )
{
    // Mirrors inventory::most_appropriate_painkiller, so the character only
    // stocks painkillers the NPC AI already knows how to use.
    const itype_id &id = it.typeId();
    return id == itype_aspirin || id == itype_acetaminophen || id == itype_ibuprofen ||
           id == itype_codeine || id == itype_oxycodone || id == itype_tramadol ||
           id == itype_heroin;
}

bool is_healing_item( const item &it )
{
    return it.is_medical_tool();
}

// Same patch of skin?  Sub-part granularity where both sides have it, the
// same the engine's own conflict rule uses (outfit::check_rigid_conflicts):
// kneepads and shin guards share a leg but not a sub-part.  A towel and most
// old-format garments carry no sub-bodypart armor data at all, so
// get_covered_sub_body_parts() comes back empty for them and the fine check
// would report no overlap no matter what -- whole-bodypart coverage is the
// fallback, since every armor entry has that much.
bool shares_sub_part( const item &a, const item &b )
{
    const std::vector<sub_bodypart_id> a_parts = a.get_covered_sub_body_parts();
    const std::vector<sub_bodypart_id> b_parts = b.get_covered_sub_body_parts();
    if( !a_parts.empty() && !b_parts.empty() ) {
        for( const sub_bodypart_id &sbp : a_parts ) {
            if( std::find( b_parts.begin(), b_parts.end(), sbp ) != b_parts.end() ) {
                return true;
            }
        }
        return false;
    }
    return a.get_covered_body_parts().make_intersection( b.get_covered_body_parts() ).any();
}

// Same sub-part *and* same layer as something worn: that is the redundancy
// (second pair of pants, second shirt on normal layer), where an undershirt
// under a hoodie is not.
bool shares_layer_and_sub_part( const item &a, const item &b )
{
    if( !shares_sub_part( a, b ) ) {
        return false;
    }
    const std::vector<sub_bodypart_id> a_parts = a.get_covered_sub_body_parts();
    const std::vector<sub_bodypart_id> b_parts = b.get_covered_sub_body_parts();
    if( !a_parts.empty() && !b_parts.empty() ) {
        for( const sub_bodypart_id &sbp : a_parts ) {
            if( std::find( b_parts.begin(), b_parts.end(), sbp ) == b_parts.end() ) {
                continue;
            }
            const std::vector<layer_level> a_layers = a.get_layer( sbp );
            const std::vector<layer_level> b_layers = b.get_layer( sbp );
            for( const layer_level &l : a_layers ) {
                if( std::find( b_layers.begin(), b_layers.end(), l ) != b_layers.end() ) {
                    return true;
                }
            }
        }
        return false;
    }
    for( const bodypart_str_id &bp : a.get_covered_body_parts() ) {
        if( !b.covers( bp.id() ) ) {
            continue;
        }
        const std::vector<layer_level> a_layers = a.get_layer( bp.id() );
        const std::vector<layer_level> b_layers = b.get_layer( bp.id() );
        for( const layer_level &l : a_layers ) {
            if( std::find( b_layers.begin(), b_layers.end(), l ) != b_layers.end() ) {
                return true;
            }
        }
    }
    return false;
}

// can_wear() only forbids a second rigid piece, so the soft redundancy is asked
// about separately.
bool conflicts_with_worn( const Character &who, const item &candidate )
{
    bool conflict = false;
    who.visit_items( [&]( const item * node, item * ) {
        if( who.is_worn( *node ) && shares_layer_and_sub_part( *node, candidate ) ) {
            conflict = true;
            return VisitResponse::ABORT;
        }
        return VisitResponse::NEXT;
    } );
    return conflict;
}

// ---------------------------------------------------------------------------
// Scoring
// ---------------------------------------------------------------------------

units::temperature planning_temperature( const Character &who )
{
    const units::temperature now = get_weather().get_temperature( who.pos_bub() );
    return now - units::from_celsius_delta( night_margin_c );
}

int target_warmth_for( units::temperature planning )
{
    const double c = units::to_celsius( planning );
    if( c >= comfort_temperature_c ) {
        return 0;
    }
    return std::min( 100, static_cast<int>( ( comfort_temperature_c - c ) * warmth_per_degree ) );
}

// An answer that holds for one turn of one order: dropped as soon as the turn
// moves on or reset_gear_up_caches() is called, which is also what every
// action the order takes does.
template<typename Key, typename Value>
class scan_cache
{
    public:
        Value *find( const Key &key ) {
            refresh();
            const auto found = entries.find( key );
            return found == entries.end() ? nullptr : &found->second;
        }
        Value &store( const Key &key, Value value ) {
            refresh();
            return entries.insert_or_assign( key, std::move( value ) ).first->second;
        }
    private:
        void refresh() {
            if( turn != calendar::turn || generation != gear_up_cache_generation ) {
                turn = calendar::turn;
                generation = gear_up_cache_generation;
                entries.clear();
            }
        }
        std::map<Key, Value> entries;
        time_point turn = calendar::before_time_starts;
        unsigned int generation = 0;
};

using outfit_pieces = std::vector<const item *>;

outfit_pieces worn_pieces( const Character &who )
{
    outfit_pieces pieces;
    who.worn.inv_dump( pieces );
    return pieces;
}

bool contains_piece( const outfit_pieces &pieces, const item *piece )
{
    return std::find( pieces.begin(), pieces.end(), piece ) != pieces.end();
}

double total_hit_size( const Character &who )
{
    double total = 0.0;
    for( const bodypart_id &bp : who.get_all_body_parts() ) {
        total += bp->hit_size;
    }
    return total;
}

// Plates seated in the ablative pockets of an armour piece.  They are part of
// the armour, not its contents.
std::vector<const item *> plates_in( const item &it )
{
    std::vector<const item *> plates;
    for( const item_pocket *pocket : it.get_ablative_pockets() ) {
        if( !pocket->empty() ) {
            plates.push_back( &pocket->front() );
        }
    }
    return plates;
}

// Pockets that hold what a character carries.  A plate pocket takes plates and
// nothing else, so it is not somewhere to put a backup blade.
bool carries_things( const item_pocket &pocket )
{
    return item_pocket::ok_default_containers( pocket ) && !pocket.is_ablative();
}

// An insert for an ablative pocket: armour that cannot be worn on its own.
bool is_plate( const item &it )
{
    return it.is_armor() && it.has_flag( flag_CANT_WEAR );
}

bool holds_loose_items( const item &it )
{
    const std::vector<const item *> plates = plates_in( it );
    for( const item *inner : it.all_items_top( pocket_type::CONTAINER ) ) {
        if( std::find( plates.begin(), plates.end(), inner ) == plates.end() ) {
            return true;
        }
    }
    return false;
}

// A respirator or a hazmat suit is worn for what it keeps out, which the order
// cannot see from here.  Nobody strips a gas mask for a slightly better hat.
bool keeps_the_air_out( const item &it )
{
    return it.has_flag( flag_GAS_PROOF ) ||
           ( it.covers( body_part_mouth.id() ) && it.get_env_resist() >= env_resist_respirator );
}

// Gear that makes a fight harder in ways the encumbrance model cannot see.
bool hinders_a_fight( const item &it )
{
    return it.has_flag( flag_BLIND ) || it.has_flag( flag_DEAF ) || it.has_flag( flag_MUTE ) ||
           it.has_flag( flag_FIN ) || it.has_flag( flag_REQUIRES_BALANCE ) ||
           it.has_flag( flag_ROLLER_ONE ) || it.has_flag( flag_ROLLER_QUAD ) ||
           it.has_flag( flag_ROLLER_INLINE ) || it.has_flag( flag_ITEM_BROKEN );
}

// A splint is armour only for a limb that is broken and not yet being mended.
bool splints_a_break( const Character &who, const item &it )
{
    if( !it.has_flag( flag_SPLINT ) ) {
        return false;
    }
    for( const bodypart_id &bp : who.get_all_body_parts( get_body_part_flags::only_main ) ) {
        if( it.covers( bp ) && who.is_limb_broken( bp ) &&
            !who.has_effect( effect_mending, bp.id() ) ) {
            return true;
        }
    }
    return false;
}

// What one piece brings to an outfit, worked out once a turn.  `worth` is what
// does not depend on the rest of the outfit: protection as the engine would
// roll it, per body part, weighted by how often that part is the one struck.
// Plates in an ablative pocket are armour too.
struct garment_facts {
    double worth = 0.0;
    double liters = 0.0;
    std::map<bodypart_id, double> coverage;
    std::map<bodypart_id, int> warmth;
    std::map<bodypart_id, std::array<double, hit_kinds>> resist;
};

// What the piece stops where it stands, per body part and damage type, as the
// engine would roll it: resistance times the share of hits it is in the way of.
void add_resist( const Character &who, const item &it, double scale, garment_facts &facts )
{
    for( const bodypart_id &bp : who.get_all_body_parts() ) {
        if( !it.covers( bp, false ) ) {
            continue;
        }
        std::array<double, hit_kinds> &stopped = facts.resist[bp];
        for( size_t i = 0; i < hit_kinds; i++ ) {
            stopped[i] += scale * it.get_coverage( bp ) / 100.0 *
                          it.resist( reference_hits[i].first, false, bp );
        }
    }
}

const garment_facts &facts_of( const Character &who, const item &it )
{
    static scan_cache<std::pair<character_id, const item *>, garment_facts> cache;
    const std::pair<character_id, const item *> key( who.getID(), &it );
    if( const garment_facts *known = cache.find( key ) ) {
        return *known;
    }
    garment_facts facts;
    const double scale = it.has_flag( flag_FRAGILE ) ? 0.5 : 1.0;
    add_resist( who, it, scale, facts );
    units::mass mass = it.weight( false );
    for( const item *plate : plates_in( it ) ) {
        add_resist( who, *plate, scale, facts );
        mass += plate->weight();
    }
    facts.worth = it.get_env_resist() * 0.2 - units::to_kilogram( mass ) * weight_per_kilogram;
    if( it.is_filthy() ) {
        facts.worth -= filth_penalty;
    }
    if( splints_a_break( who, it ) ) {
        facts.worth += weight_splint;
    }
    if( it.has_flag( flag_RESTRICT_HANDS ) ) {
        item_location wielded = who.get_wielded_item();
        facts.worth -= wielded && wielded->is_two_handed( who ) ? weight_hands_taken_armed :
                       weight_hands_taken;
    }
    facts.liters = units::to_liter( it.get_volume_capacity( carries_things ) );
    for( const bodypart_id &bp : who.get_all_body_parts() ) {
        if( it.covers( bp, false ) ) {
            facts.coverage[bp] = it.get_coverage( bp ) / 100.0;
        }
    }
    std::vector<std::pair<bodypart_id, int>> warmth;
    it.get_warmth_by_bodypart( warmth );
    for( const std::pair<bodypart_id, int> &entry : warmth ) {
        facts.warmth[entry.first] += entry.second;
    }
    return cache.store( key, std::move( facts ) );
}

double storage_worth( double liters )
{
    const double credited = std::min( liters, want_storage_liters );
    return credited * weight_storage_per_liter +
           ( liters - credited ) * weight_storage_marginal +
           weight_storage_floor * std::min( liters, want_storage_liters_floor ) /
           want_storage_liters_floor;
}

// Pocket the character has that no worn piece accounts for.
double unworn_liters( const Character &who )
{
    double liters = units::to_liter( who.volume_capacity( carries_things ) );
    for( const item *piece : worn_pieces( who ) ) {
        liters -= facts_of( who, *piece ).liters;
    }
    return std::max( 0.0, liters );
}

// What the outfit is worth with some pieces off and one more on: protection,
// no bare skin, warmth up to what the weather asks for, pockets.  Everything
// here is a sum over pieces except the three that saturate -- skin, warmth and
// storage -- which is why it is asked of the whole outfit.
double outfit_worth( Character &who, const outfit_pieces &removing, const item *adding )
{
    const double total_hit = total_hit_size( who );
    const int target_warmth = target_warmth_for( planning_temperature( who ) );
    std::map<bodypart_id, double> best_cover;
    std::map<bodypart_id, int> warmth;
    std::map<bodypart_id, std::array<double, hit_kinds>> layered;
    double worth = 0.0;
    double liters = unworn_liters( who );
    const auto count = [&]( const garment_facts & facts ) {
        worth += facts.worth;
        liters += facts.liters;
        for( const std::pair<const bodypart_id, std::array<double, hit_kinds>> &stopped :
             facts.resist ) {
            std::array<double, hit_kinds> &sum = layered[stopped.first];
            for( size_t i = 0; i < sum.size(); i++ ) {
                sum[i] += stopped.second[i];
            }
        }
        for( const std::pair<const bodypart_id, double> &cover : facts.coverage ) {
            best_cover[cover.first] = std::max( best_cover[cover.first], cover.second );
        }
        for( const std::pair<const bodypart_id, int> &heat : facts.warmth ) {
            warmth[heat.first] += heat.second;
        }
    };
    for( const item *piece : worn_pieces( who ) ) {
        if( !contains_piece( removing, piece ) ) {
            count( facts_of( who, *piece ) );
        }
    }
    if( adding ) {
        count( facts_of( who, *adding ) );
    }
    for( const bodypart_id &bp : who.get_all_body_parts() ) {
        const double share = bp->hit_size / total_hit;
        const std::array<double, hit_kinds> &stopped = layered[bp];
        for( size_t i = 0; i < stopped.size(); i++ ) {
            const double hit = reference_hits[i].second;
            worth += share * weight_hit_share * hit * ( 1.0 - std::exp( -stopped[i] / hit ) );
        }
        worth += std::max( share, share_exposure_floor ) * weight_bare_skin * weight_hit_share *
                 best_cover[bp];
        const int heat = warmth[bp];
        worth += share * ( heat <= target_warmth
                           ? heat * weight_warmth_needed
                           : target_warmth * weight_warmth_needed -
                           ( heat - target_warmth ) * weight_warmth_excess );
    }
    return worth + storage_worth( liters );
}

// The outfit as it would be with some pieces off, kept whole so that the
// encumbrance the engine would charge, contents and layering included, can be
// asked of it for every candidate without copying the character's pack each
// time.  Mutable only so that measure_form() can lend it to the character.
outfit &outfit_without( const Character &who, outfit_pieces without )
{
    static scan_cache<std::pair<character_id, outfit_pieces>, outfit> cache;
    std::sort( without.begin(), without.end(), std::less<const item *>() );
    const std::pair<character_id, outfit_pieces> key( who.getID(), without );
    if( outfit *known = cache.find( key ) ) {
        return *known;
    }
    std::list<item> kept;
    for( const item *piece : worn_pieces( who ) ) {
        if( !contains_piece( without, piece ) ) {
            kept.push_back( *piece );
        }
    }
    return cache.store( key, outfit( kept ) );
}

// How well a character does the things a fight is made of.  Every field is
// "bigger is better"; costs are stored inverted.
struct fighting_form {
    double dodging = 0.0;
    double melee_hit = 0.0;
    double melee_speed = 0.0;
    double movement = 0.0;
    double stamina = 0.0;
    double blocking = 0.0;
    double handling = 0.0;
    double sight = 0.0;
    double grip = 0.0;
};

// Lets the engine's own limb scores and character modifiers speak for the
// outfit with some pieces off and one more on, then puts back what the
// character really wears.  Mutations, body mass, wounds and effects are
// therefore in the answer without being modelled here.
fighting_form measure_form( Character &who, const outfit_pieces &removing, const item *adding )
{
    outfit *hypothetical = removing.empty() ? nullptr : &outfit_without( who, removing );
    if( hypothetical ) {
        std::swap( who.worn, *hypothetical );
    }
    who.calc_encumbrance( adding ? *adding : null_item_reference() );
    const auto inverse = []( double cost ) {
        return cost > std::numeric_limits<float>::epsilon() ? 1.0 / cost : 0.0;
    };
    fighting_form form;
    form.dodging = who.get_modifier( character_modifier_limb_dodge_mod ) *
                   who.get_limb_score( limb_score_reaction );
    form.melee_hit = who.get_modifier( character_modifier_melee_attack_roll_mod );
    form.melee_speed =
        inverse( who.get_modifier( character_modifier_melee_thrown_move_balance_mod ) );
    form.movement = inverse( who.get_modifier( character_modifier_limb_run_cost_mod ) );
    form.stamina = who.get_modifier( character_modifier_stamina_recovery_breathing_mod );
    form.blocking = who.get_limb_score( limb_score_block );
    form.handling = inverse( who.get_modifier( character_modifier_reloading_move_mod ) );
    form.sight = who.get_limb_score( limb_score_vision );
    form.grip = who.get_limb_score( limb_score_grip );
    if( hypothetical ) {
        std::swap( who.worn, *hypothetical );
    }
    who.calc_encumbrance();
    return form;
}

// How much of the coming fight is shooting: a gun in hand is all of it, one in
// the pack half.
double shooting_share( const Character &who )
{
    static scan_cache<character_id, double> cache;
    if( const double *known = cache.find( who.getID() ) ) {
        return *known;
    }
    double share = 0.0;
    item_location wielded = who.get_wielded_item();
    if( wielded && wielded->is_gun() ) {
        share = 1.0;
    } else {
        who.visit_items( [&share]( const item * node, item * ) {
            if( node->is_gun() ) {
                share = 0.5;
                return VisitResponse::ABORT;
            }
            return VisitResponse::NEXT;
        } );
    }
    return cache.store( who.getID(), share );
}

// Unclothed, with whatever the character's own body and mutations already cost.
const fighting_form &unencumbered_form( Character &who )
{
    static scan_cache<character_id, fighting_form> cache;
    if( const fighting_form *known = cache.find( who.getID() ) ) {
        return *known;
    }
    return cache.store( who.getID(), measure_form( who, worn_pieces( who ), nullptr ) );
}

// What an outfit's encumbrance costs, in armour points.
double efficiency_lost( Character &who, const outfit_pieces &removing, const item *adding )
{
    const fighting_form &whole = unencumbered_form( who );
    const fighting_form kept = measure_form( who, removing, adding );
    const double shooting = shooting_share( who );
    // A limb pushed past what it can bear scores nothing, which would be a
    // loss without end; this is as bad as it is allowed to read.
    constexpr double least_kept = 0.02;
    const auto lost = []( double was, double now, double weight ) {
        if( was <= 0.0 ) {
            return 0.0;
        }
        const double kept = std::max( now, was * least_kept );
        const double shortfall = std::max( 0.0, std::log( was / kept ) );
        return weight * shortfall * shortfall;
    };
    double total = 0.0;
    total += lost( whole.dodging, kept.dodging, 1.0 );
    total += lost( whole.melee_hit, kept.melee_hit, 0.5 );
    total += lost( whole.melee_speed, kept.melee_speed, 0.4 );
    total += lost( whole.movement, kept.movement, 1.0 );
    total += lost( whole.stamina, kept.stamina, 0.8 );
    total += lost( whole.blocking, kept.blocking, 0.4 );
    total += lost( whole.handling, kept.handling, 0.3 + 0.5 * shooting );
    total += lost( whole.sight, kept.sight, 0.4 + 0.5 * shooting );
    total += lost( whole.grip, kept.grip, 0.3 );
    return total * weight_efficiency_lost;
}

// Where the outfit stands now, so that a change is judged against it.
struct outfit_standing {
    double worth = 0.0;
    double lost = 0.0;
};

const outfit_standing &standing_of( Character &who )
{
    static scan_cache<character_id, outfit_standing> cache;
    if( const outfit_standing *known = cache.find( who.getID() ) ) {
        return *known;
    }
    outfit_standing now;
    now.worth = outfit_worth( who, {}, nullptr );
    now.lost = efficiency_lost( who, {}, nullptr );
    return cache.store( who.getID(), now );
}

// What taking `removing` off and putting `adding` on would do to the character,
// in armour points: the outfit's worth, less what its encumbrance costs.
// Positive means better prepared.
double change_gain( Character &who, const outfit_pieces &removing, const item *adding )
{
    const outfit_standing &now = standing_of( who );
    const double worth = outfit_worth( who, removing, adding ) - now.worth;
    // Encumbrance can at best give back what it costs now, so a change that
    // does not pay even then is not worth measuring.
    if( worth + now.lost <= margin_garment ) {
        return worth + now.lost;
    }
    return worth - ( efficiency_lost( who, removing, adding ) - now.lost );
}


// The finest set of plate in the county is worthless to someone who collapses
// from heatstroke wearing it, so somebody already overheating puts nothing
// else on.  Only the hot side: someone freezing needs clothes more than
// anybody, and refusing to hand them a coat would be the opposite of help.
bool overheating_forbids_dressing( const Character &who )
{
    for( const bodypart_id &bp : who.get_all_body_parts() ) {
        if( who.get_part_temp_conv( bp ) >= BODYTEMP_VERY_HOT ) {
            return true;
        }
    }
    return false;
}

// ---------------------------------------------------------------------------
// Zone-aware search and placement
// ---------------------------------------------------------------------------

bool tile_is_off_limits( const Character &who, const tripoint_bub_ms &tile )
{
    // Loot: Ignore is the player saying "leave this pile alone", which holds
    // whoever is doing the sorting.
    if( g->check_zone( zone_type_LOOT_IGNORE, tile ) ) {
        return true;
    }
    const npc *guy = who.as_npc();
    if( !guy ) {
        return false;
    }
    // The rest is about NPCs specifically: a zone marked hands-off to them,
    // and anywhere this one has been told not to go.
    return g->check_zone( zone_type_NO_NPC_PICKUP, tile ) ||
           guy->is_no_go_position( get_map().get_abs( tile ) );
}

// Every loot zone the faction owns, plus the basecamp's own storage and food
// zones, which do not carry the LOOT prefix.  Specific zones and the big
// general one laid over them overlap heavily; the set deduplicates.  NPC and
// avatar look at exactly the same set -- relying on which specific LOOT_*
// zone types exist would be its own kind of fragile -- and lean on the
// existing exceptions (NO_NPC_PICKUP, LOOT_IGNORE, favourites, someone else's
// property, a no-go position) to keep an NPC out of what it should not touch.
// Everywhere worth looking: every loot zone the faction owns, the basecamp's
// own storage and food zones which do not carry the LOOT prefix, and what is
// within arm's reach of those and of the character.
//
// The zones say where a camp keeps things -- specific LOOT_* zones and the big
// general one laid over them overlap heavily, so the set deduplicates, and
// reading them all beats relying on which specific types exist.  But a camp is
// not only its zones: the dresser in the corner of the store room holds
// clothes whether or not anyone drew a box round it, and getting ready for a
// fight while a rack of armour two steps away goes unread is the order failing
// at the one thing it is for.  Somebody caught away from their camp entirely
// still gets what is around them, which is when being ready matters most.
//
// Arm's reach rather than view distance, because past that it stops being
// "what is around me".  What keeps this honest rather than a licence to strip
// a town is the exceptions it already leans on: NO_NPC_PICKUP, LOOT_IGNORE, a
// no-go position, favourites, and above all somebody else's property, which
// off_limits_item() leaves exactly where it is.
std::unordered_set<tripoint_abs_ms> stores_within_reach( Character &who )
{
    zone_manager &mgr = zone_manager::get_manager();
    map &here = get_map();
    const faction_id fac = who.get_faction_id();

    std::vector<tripoint_bub_ms> anchors;
    anchors.push_back( who.pos_bub() );
    for( const tripoint_bub_ms &tile :
         mgr.get_point_set_loot( who.pos_abs(), MAX_VIEW_DISTANCE, who.is_npc(), fac ) ) {
        anchors.push_back( tile );
    }
    for( const zone_type_id &type : {
             zone_type_CAMP_STORAGE, zone_type_CAMP_FOOD
         } ) {
        for( const tripoint_abs_ms &tile :
             mgr.get_near( type, who.pos_abs(), MAX_VIEW_DISTANCE, nullptr, fac ) ) {
            anchors.push_back( here.get_bub( tile ) );
        }
    }

    std::unordered_set<tripoint_abs_ms> tiles;
    for( const tripoint_bub_ms &anchor : anchors ) {
        if( !here.inbounds( anchor ) ) {
            // Outside the reality bubble: keep the zone tile itself so the
            // framework can route there and decide once it can see it.
            tiles.emplace( here.get_abs( anchor ) );
            continue;
        }
        for( const tripoint_bub_ms &tile : here.points_in_radius( anchor, PICKUP_RANGE ) ) {
            if( here.inbounds( tile ) && !tile_is_off_limits( who, tile ) ) {
                tiles.emplace( here.get_abs( tile ) );
            }
        }
    }
    return tiles;
}

// Where does this belong?  The zone manager already knows -- the same
// question the loot sorter asks -- so putting things down here leaves the
// camp sorted instead of piled wherever we stood.
std::optional<tripoint_bub_ms> home_for( Character &who, const item &it,
        const tripoint_bub_ms &fallback )
{
    zone_manager &mgr = zone_manager::get_manager();
    map &here = get_map();
    const faction_id fac = who.get_faction_id();

    const zone_type_id dest =
        mgr.get_near_zone_type_for_item( it, who.pos_abs(), MAX_VIEW_DISTANCE, fac );

    std::vector<zone_type_id> tries;
    if( !dest.is_empty() ) {
        tries.push_back( dest );
    }
    tries.push_back( zone_type_CAMP_STORAGE );
    tries.push_back( zone_type_LOOT_UNSORTED );

    for( const zone_type_id &type : tries ) {
        std::optional<tripoint_bub_ms> best;
        int best_dist = INT_MAX;
        for( const tripoint_abs_ms &spot :
             mgr.get_near( type, who.pos_abs(), MAX_VIEW_DISTANCE, &it, fac ) ) {
            const tripoint_bub_ms bub = here.get_bub( spot );
            if( !here.inbounds( bub ) || tile_is_off_limits( who, bub ) ) {
                continue;
            }
            const int dist = rl_dist( who.pos_bub(), bub );
            if( dist < best_dist ) {
                best_dist = dist;
                best = bub;
            }
        }
        if( best ) {
            return best;
        }
    }
    if( here.inbounds( fallback ) ) {
        return fallback;
    }
    return std::nullopt;
}

// Somewhere sensible for a displaced piece: the zone the zone manager picks
// for it, never the character's own pockets.  A displaced piece is camp
// property being put away, not a keepsake -- whoever is doing the gearing up
// is standing in the camp already, so there is nowhere better to carry it to,
// and one character's "might need it later" is everyone else's item made
// unavailable and everyone's carry weight made worse for nothing.  False
// means even that failed, and every caller answers that by putting it down on
// the crate rather than losing it -- also in the camp, so no worse a home.
// Put one item down on a tile, into the trunk if the tile is one.  Vehicle
// cargo and ground are the same two places candidates_at() reads from, so
// leaving a displaced coat on the floor under the truck it came out of would
// be the sweep unsorting the camp it just read.
bool place_at( const tripoint_bub_ms &tile, const item &it )
{
    map &here = get_map();
    if( const std::optional<vpart_reference> vp = here.veh_at( tile ).cargo() ) {
        if( vp->vehicle().add_item( here, vp->part(), it ) ) {
            return true;
        }
        // A full trunk is not a lost item; the ground beside it will do.
    }
    return !here.add_item_or_charges( tile, it ).is_null();
}

bool put_away( Character &who, const item &it, const tripoint_bub_ms &fallback )
{
    const std::optional<tripoint_bub_ms> home = home_for( who, it, fallback );
    if( !home ) {
        return false;
    }
    return place_at( *home, it );
}

// ---------------------------------------------------------------------------
// Moving items around
// ---------------------------------------------------------------------------

bool take_into_inventory( Character &who, item_location &loc )
{
    if( !loc ) {
        return false;
    }
    const item copy = *loc;
    // can_stash only asks about volume.  Ammunition and rations are heavy, and
    // someone weighed down below walking pace has been made worse, not better.
    if( who.weight_carried() + copy.weight() > who.weight_capacity() ) {
        return false;
    }
    if( !who.can_stash( copy ) || !who.i_add( copy ) ) {
        return false;
    }
    who.mod_moves( -handle_cost_moves );
    loc.remove_item();
    return true;
}

// The same, for part of a charge-based stack such as ammunition or water.
int take_charges( Character &who, item_location &loc, int wanted )
{
    if( !loc || wanted <= 0 ) {
        return 0;
    }
    const int available = loc->count();
    int take = std::min( available, wanted );
    if( take <= 0 ) {
        return 0;
    }
    item copy = *loc;
    if( copy.count_by_charges() ) {
        copy.charges = take;
        // Take what can actually be carried rather than all or nothing.
        const std::int64_t stack_grams = std::max<std::int64_t>( 1, to_gram( copy.weight() ) );
        const std::int64_t headroom_grams =
            to_gram( who.weight_capacity() ) - to_gram( who.weight_carried() );
        if( stack_grams > headroom_grams ) {
            take = static_cast<int>( std::max<std::int64_t>( 0,
                                     headroom_grams * take / stack_grams ) );
            if( take <= 0 ) {
                return 0;
            }
            copy.charges = take;
        }
    } else {
        take = 1;
    }
    if( who.weight_carried() + copy.weight() > who.weight_capacity() ) {
        return 0;
    }
    if( !who.can_stash( copy ) || !who.i_add( copy ) ) {
        return 0;
    }
    who.mod_moves( -handle_cost_moves );
    if( loc->count_by_charges() && loc->charges > take ) {
        loc->charges -= take;
    } else {
        loc.remove_item();
    }
    return take;
}

// takeoff() without the "<npcname> takes off their X" line, so that trial
// fittings do not bury what the character actually decided.
bool quiet_takeoff( Character &who, item_location loc, std::list<item> &into )
{
    if( !loc || !who.can_takeoff( *loc, &into ).success() ) {
        return false;
    }
    if( !who.worn.takeoff( loc, &into, who ) ) {
        return false;
    }
    who.recalc_sight_limits();
    who.calc_encumbrance();
    who.worn.recalc_ablative_blocking( &who );
    who.calc_discomfort();
    return true;
}

// npc::wield and avatar::wield each do bookkeeping of their own on top of
// Character::wield -- martial arts styles, the range cache, the message -- and
// none of the three is virtual, so a Character-typed call silently skips it.
bool wield_loc( Character &who, item_location loc )
{
    if( npc *guy = who.as_npc() ) {
        return guy->wield( loc );
    }
    if( avatar *me = who.as_avatar() ) {
        return me->wield( loc );
    }
    return who.wield( loc );
}

// can_reload() says yes for items that then refuse the load itself -- a folded
// bow keeps its ammo type but loses the pocket -- and npc::do_reload answers a
// refused load with a debugmsg, so ask here first.
bool has_room_for_a_load( const item &target )
{
    if( target.is_gun() && !target.magazine_integral() ) {
        // A magazine well takes a magazine, not loose rounds: it is free when
        // it is empty, and worth topping up when the magazine in it is not.
        const item *mag = target.magazine_current();
        return !mag || !mag->is_magazine_full();
    }
    return target.remaining_ammo_capacity() > 0;
}

bool try_reload( Character &who, item_location target )
{
    if( !target || !has_room_for_a_load( *target ) || !who.can_reload( *target ) ) {
        return false;
    }
    if( npc *guy = who.as_npc() ) {
        if( !guy->find_usable_ammo( target ) ) {
            return false;
        }
        guy->do_reload( target );
        return true;
    }
    // The avatar's own select_ammo() prompts, which an activity must not do, so
    // the load is found by hand: a magazine feeds a magazine-fed gun, loose
    // rounds feed magazines and integral wells.  Whatever is already inside the
    // target is not a load for it.
    const auto usable = [&target]( const item_location & carried ) {
        return carried && carried.get_item() != target.get_item() &&
               !target->has_item( *carried );
    };
    item_location load;
    int qty = 0;
    if( target->is_gun() && !target->magazine_integral() ) {
        const std::set<itype_id> compatible = target->magazine_compatible();
        for( item_location &carried : who.all_items_loc() ) {
            if( usable( carried ) && carried->is_magazine() &&
                compatible.count( carried->typeId() ) > 0 && carried->ammo_remaining() > 0 &&
                ( !load || carried->ammo_remaining() > load->ammo_remaining() ) ) {
                load = carried;
            }
        }
        qty = 1;
    } else {
        const std::set<ammotype> types = target->ammo_types();
        for( item_location &carried : who.all_items_loc() ) {
            if( usable( carried ) && carried->is_ammo() &&
                types.count( carried->ammo_type() ) > 0 &&
                ( !load || carried->charges > load->charges ) ) {
                load = carried;
            }
        }
        if( load ) {
            qty = std::min( load->count(), target->remaining_ammo_capacity() );
        }
    }
    if( !load || qty <= 0 ) {
        return false;
    }
    const std::string target_name = target->tname();
    who.mod_moves( -who.item_reload_cost( *target, *load, qty ) );
    if( !target->reload( who, std::move( load ), qty ) ) {
        return false;
    }
    who.add_msg_if_player( m_good, _( "You reload the %s." ), target_name );
    return true;
}

// Find a carried item of this type again after it has been stowed -- the
// location it had before the move is not the one it has now.
item_location find_carried( Character &who, const itype_id &id )
{
    for( item_location &loc : who.all_items_loc() ) {
        if( loc && loc->typeId() == id && !who.is_worn( *loc ) && !who.is_wielding( *loc ) ) {
            return loc;
        }
    }
    return {};
}

// Count all ammunition matching types on the character -- loose rounds in
// pockets, rounds inside spare magazines, and rounds currently loaded into
// carried or wielded guns.  visit_items() descends CONTAINER pockets only,
// so rounds in a magazine pocket are invisible without this.
int count_ammo_carried( const Character &who, const std::set<ammotype> &types )
{
    int total = 0;
    who.visit_items( [&total, &types]( const item * node, item * ) {
        if( node->is_ammo() && types.count( node->ammo_type() ) > 0 ) {
            total += node->count();
        } else if( ( node->is_gun() || node->is_magazine() ) && node->ammo_remaining() > 0 ) {
            for( const ammotype &at : node->ammo_types() ) {
                if( types.count( at ) > 0 ) {
                    total += node->ammo_remaining();
                    break;
                }
            }
        }
        return VisitResponse::NEXT;
    } );
    return total;
}

int count_carried( const Character &who, const std::function<bool( const item & )> &pred )
{
    int total = 0;
    who.visit_items( [&total, &pred]( const item * node, item * ) {
        if( pred( *node ) ) {
            total += node->count();
        }
        return VisitResponse::NEXT;
    } );
    return total;
}

// ---------------------------------------------------------------------------
// Candidates on one tile
// ---------------------------------------------------------------------------

// Favourites are the player's word on the subject, at any depth.  Somebody
// else's property is theirs: the wield path would stop and ask about it, and
// an activity working through a whole camp cannot stop and ask about
// everything, so it leaves those alone instead.
bool off_limits_item( const Character &who, const item &it )
{
    return it.is_favorite || it.made_of( phase_id::LIQUID ) ||
           !it.is_owned_by( who, true );
}

// Wearing a bag empties it into the camp's zones first, so one holding
// something the player marked keeps its place on the shelf: a favourite is
// not to be taken, and not to be moved either.
bool holds_a_favorite( const item &it )
{
    bool found = false;
    for( const item *inner : it.all_items_top( pocket_type::CONTAINER ) ) {
        inner->visit_items( [&found]( const item * node, item * ) {
            if( node->is_favorite ) {
                found = true;
                return VisitResponse::ABORT;
            }
            return VisitResponse::NEXT;
        } );
        if( found ) {
            return true;
        }
    }
    return false;
}

// Everything nested inside crates, boxes, duffel bags and first aid kits,
// which is where a sorted camp keeps things.  The plates seated in a carrier
// are part of the carrier, not stored in it.
void collect_from( const Character &who, item_location parent,
                   std::vector<item_location> &out, int depth )
{
    if( depth > max_nesting_depth ) {
        return;
    }
    const std::vector<const item *> plates = plates_in( *parent );
    for( item *inner : parent->all_items_top( pocket_type::CONTAINER ) ) {
        if( off_limits_item( who, *inner ) ||
            std::find( plates.begin(), plates.end(), inner ) != plates.end() ) {
            continue;
        }
        item_location child( parent, inner );
        out.push_back( child );
        collect_from( who, child, out, depth + 1 );
    }
}

// No line-of-sight test here, deliberately, and none in
// tile_has_anything_wanted() either.  map::could_see_items() answers false for
// a tile of container furniture -- a locker, a dresser, a crate -- unless the
// character is standing next to it, which is exactly the furniture a camp
// keeps its clothes in.  Gating on it means a locker across the room is never
// worth walking to, because you cannot see inside it until you have walked
// there: the character loots whatever is within arm's reach and reports the
// job done.  Loot sorting reads its own zone tiles without asking, and these
// are the same tiles, in the character's own camp.
// Ground and vehicle cargo both, the same two places zone_sorting's own
// populate_items() reads: a camp that keeps its stores in the back of a truck
// hands those tiles back from the zone manager like any other, and reading
// only the ground means walking to the trunk and standing there.
std::vector<item_location> candidates_at( Character &who, const tripoint_bub_ms &tile )
{
    std::vector<item_location> out;
    map &here = get_map();
    if( !here.inbounds( tile ) ) {
        return out;
    }
    const auto offer = [&who, &out]( item & it, const item_location & loc ) {
        if( off_limits_item( who, it ) ) {
            return;
        }
        out.push_back( loc );
        collect_from( who, loc, out, 1 );
    };
    if( const std::optional<vpart_reference> vp = here.veh_at( tile ).cargo() ) {
        for( item &it : vp->items() ) {
            offer( it, item_location( vehicle_cursor( vp->vehicle(), vp->part_index() ), &it ) );
        }
    }
    for( item &it : here.i_at( tile ) ) {
        offer( it, item_location( map_cursor( tile ), &it ) );
    }
    return out;
}

// Plates lying about the camp, best first.  Seated ones are not: they belong
// to the carrier they are in.
const std::vector<const item *> &plates_in_reach( Character &p )
{
    static scan_cache<character_id, std::vector<const item *>> cache;
    if( const std::vector<const item *> *known = cache.find( p.getID() ) ) {
        return *known;
    }
    std::vector<const item *> plates;
    map &here = get_map();
    for( const tripoint_abs_ms &tile : stores_within_reach( p ) ) {
        const tripoint_bub_ms bub = here.get_bub( tile );
        if( !here.inbounds( bub ) ) {
            continue;
        }
        for( item_location &loc : candidates_at( p, bub ) ) {
            if( loc && is_plate( *loc ) ) {
                plates.push_back( loc.get_item() );
            }
        }
    }
    std::stable_sort( plates.begin(), plates.end(), [&p]( const item * a, const item * b ) {
        return facts_of( p, *a ).worth > facts_of( p, *b ).worth;
    } );
    return cache.store( p.getID(), std::move( plates ) );
}

// The piece as it would be worn: a bag arrives empty because wearing one
// empties it into the camp's zones first, but the plates of a carrier stay
// where they are, being armour, and an empty carrier is judged with the best
// plates the camp can put in it, since those are what it is worn for.  Judged
// as it would be worn, and only actually emptied once the decision is made,
// so that a coat turned down leaves the camp's crates as it found them.
const item &as_worn( Character &p, const item &it )
{
    static scan_cache<std::pair<character_id, const item *>, item> cache;
    if( it.all_items_top( pocket_type::CONTAINER ).empty() && !it.is_ablative() ) {
        return it;
    }
    const std::pair<character_id, const item *> key( p.getID(), &it );
    if( const item *known = cache.find( key ) ) {
        return *known;
    }
    item emptied( it );
    const std::vector<const item *> plates = plates_in( emptied );
    for( item *inner : emptied.all_items_top( pocket_type::CONTAINER ) ) {
        if( std::find( plates.begin(), plates.end(), inner ) == plates.end() ) {
            emptied.remove_item( *inner );
        }
    }
    std::vector<const item *> used;
    for( item_pocket *pocket : emptied.get_ablative_pockets() ) {
        if( !pocket->empty() ) {
            continue;
        }
        for( const item *plate : plates_in_reach( p ) ) {
            if( !contains_piece( used, plate ) && pocket->can_contain( *plate ).success() &&
                emptied.put_in( *plate, pocket_type::CONTAINER, false, nullptr, true ).success() ) {
                used.push_back( plate );
                break;
            }
        }
    }
    return cache.store( key, std::move( emptied ) );
}

// ---------------------------------------------------------------------------
// Wants
//
// One predicate answers both "is this tile worth walking to" and "what do I do
// now that I am standing here".  They must agree, or the character walks
// somewhere and then does nothing, over and over.
// ---------------------------------------------------------------------------

// A camp tool (wrench, waffle iron) reads as is_melee() but must not be taken
// as a weapon; a combat knife carries a tool slot but must.  Only the item's
// own category tells them apart.  So it is with a hard hat or a boot, which
// bash well enough to outscore bare fists and are for wearing.  Guns are
// exempt -- a plasma torch is a tool.
bool is_weapon_candidate( const item &it )
{
    if( it.is_gun() ) {
        return true;
    }
    if( !it.is_melee() ) {
        return false;
    }
    return it.get_category_shallow().get_id() == item_category_weapons ||
           ( !it.is_tool() && !it.is_armor() );
}

// What the camp can load a gun with: ammunition types, and the magazines to
// put them in.  Rebuilt once a turn: the answer is the same for every candidate
// weapon on every shelf, and working it out per candidate would walk the whole
// camp for each one.
struct loading_supplies {
    std::set<ammotype> ammo;
    std::set<itype_id> magazines;
};

const loading_supplies &supplies_in_reach( Character &who )
{
    static std::map<character_id, loading_supplies> types_cache;
    static time_point cached_turn = calendar::before_time_starts;
    static unsigned int cached_generation = 0;
    if( cached_turn != calendar::turn || cached_generation != gear_up_cache_generation ) {
        cached_turn = calendar::turn;
        cached_generation = gear_up_cache_generation;
        types_cache.clear();
    }
    auto it = types_cache.find( who.getID() );
    if( it != types_cache.end() ) {
        return it->second;
    }

    loading_supplies supplies;
    const auto note = [&]( const item & itm ) {
        if( itm.is_ammo() ) {
            supplies.ammo.insert( itm.ammo_type() );
        } else if( itm.is_magazine() ) {
            supplies.magazines.insert( itm.typeId() );
            for( const ammotype &at : itm.ammo_types() ) {
                supplies.ammo.insert( at );
            }
        }
    };
    who.visit_items( [&note]( const item * node, item * ) {
        note( *node );
        return VisitResponse::NEXT;
    } );
    const auto note_pile = [&note]( item & itm ) {
        itm.visit_items( [&note]( const item * node, item * ) {
            note( *node );
            return VisitResponse::NEXT;
        } );
    };
    map &here = get_map();
    for( const tripoint_abs_ms &tile : stores_within_reach( who ) ) {
        const tripoint_bub_ms bub = here.get_bub( tile );
        if( !here.inbounds( bub ) ) {
            continue;
        }
        if( const std::optional<vpart_reference> vp = here.veh_at( bub ).cargo() ) {
            for( item &itm : vp->items() ) {
                note_pile( itm );
            }
        }
        for( item &itm : here.i_at( bub ) ) {
            note_pile( itm );
        }
    }
    return types_cache.emplace( who.getID(), std::move( supplies ) ).first->second;
}

// Is there anything to feed this gun with, anywhere the character can get at?
// A gun already holding rounds needs no further justification.  Loose rounds
// are no use to a magazine-fed gun that has no magazine, nor any in reach.
bool gun_has_ammo_in_reach( Character &who, const item &gun )
{
    if( gun.ammo_remaining() > 0 ) {
        return true;
    }
    const std::set<ammotype> wanted = gun.ammo_types();
    if( wanted.empty() ) {
        // Needs no ammunition at all: a bionic weapon, a UPS tool.
        return true;
    }
    const loading_supplies &available = supplies_in_reach( who );
    if( !gun.magazine_integral() && !gun.magazine_current() ) {
        bool has_magazine = false;
        for( const itype_id &mag : gun.magazine_compatible() ) {
            has_magazine = has_magazine || available.magazines.count( mag ) > 0;
        }
        if( !has_magazine ) {
            return false;
        }
    }
    for( const ammotype &at : wanted ) {
        if( available.ammo.count( at ) > 0 ) {
            return true;
        }
    }
    return false;
}

// Every weapon judged on the same terms.  evaluate_weapon() caches its answer
// for the item in hand and that cached path ignores pretend_have_ammo, so an
// unloaded gun scores differently in hand than on the shelf and the two swap
// places turn after turn; a copy takes the uncached path.  Pretend ammo is the
// default because ammunition is chosen after the weapon, and a gun judged
// empty can never beat a knife.
double weapon_score( const Character &p, const item &it, bool pretend_ammo = true )
{
    if( p.is_wielding( it ) ) {
        const item copy = it;
        return p.evaluate_weapon( copy, pretend_ammo );
    }
    return p.evaluate_weapon( it, pretend_ammo );
}

// What bare hands are worth.  Depends only on body and skills, neither of
// which moves during a sweep, so once a turn rather than once per item.
double unarmed_score( const Character &p )
{
    static std::map<character_id, double> score_cache;
    static time_point cached_turn = calendar::before_time_starts;
    static unsigned int cached_generation = 0;
    if( cached_turn != calendar::turn || cached_generation != gear_up_cache_generation ) {
        cached_turn = calendar::turn;
        cached_generation = gear_up_cache_generation;
        score_cache.clear();
    }
    auto it = score_cache.find( p.getID() );
    if( it != score_cache.end() ) {
        return it->second;
    }
    const double score = p.evaluate_weapon( null_item_reference(), false );
    return score_cache.emplace( p.getID(), score ).first->second;
}

// The bar every candidate is measured against, worked out once a turn: the
// copy that dodges evaluate_weapon()'s cache is not free.
double current_weapon_score( Character &p )
{
    struct entry {
        itype_id weapon;
        double score;
    };
    static std::map<character_id, entry> score_cache;
    static time_point cached_turn = calendar::before_time_starts;
    static unsigned int cached_generation = 0;

    item_location wielded = p.get_wielded_item();
    const itype_id now = wielded ? wielded->typeId() : itype_id::NULL_ID();
    if( cached_turn != calendar::turn || cached_generation != gear_up_cache_generation ) {
        cached_turn = calendar::turn;
        cached_generation = gear_up_cache_generation;
        score_cache.clear();
    }
    auto it = score_cache.find( p.getID() );
    if( it != score_cache.end() && it->second.weapon == now ) {
        return it->second.score;
    }
    const double score = wielded ? weapon_score( p, *wielded ) : unarmed_score( p );
    score_cache[p.getID()] = { now, score };
    return score;
}

// Everything asked of a weapon candidate except whether some other tile in
// reach holds a better one.  best_weapon_in_reach() scans with this, so this
// side must never call back into wants_as_weapon() or the two recurse.
bool is_weapon_upgrade( Character &p, const item &it )
{
    // A weapon this order already gave up gets no second look, or the two trade
    // places forever, each briefly ahead of the other.
    if( !is_weapon_candidate( it ) || p.gear_up_rejected.count( it.typeId() ) > 0 ||
        !p.can_wield( it ).success() ) {
        return false;
    }
    // What cannot be lifted is not an upgrade, and the hands would be emptied
    // for nothing.
    if( p.weight_carried() + it.weight() > p.weight_capacity() ) {
        return false;
    }
    // A gun with no round for it anywhere in the camp is a club with an awkward
    // grip.  Scored on pretend ammo it beats the knife already in hand.
    if( it.is_gun() && !gun_has_ammo_in_reach( p, it ) ) {
        return false;
    }
    return weapon_score( p, it ) > current_weapon_score( p );
}

// Walks every store tile in reach and remembers the single best pick, so a
// weapon or backup blade taken from the first crate visited cannot lose to
// one two tiles further on that this sweep would otherwise never compare it
// against.  Recomputed once a turn like supplies_in_reach(): stores get
// emptied and carried gear changes, and this walks the whole reachable area.
item_location best_candidate_in_reach( Character &p,
        const std::function<bool( Character &, const item & )> &wants,
        const std::function<double( Character &, const item & )> &value )
{
    item_location best;
    double best_value = 0.0;
    map &here = get_map();
    for( const tripoint_abs_ms &tile : stores_within_reach( p ) ) {
        const tripoint_bub_ms bub = here.get_bub( tile );
        if( !here.inbounds( bub ) ) {
            continue;
        }
        for( item_location &loc : candidates_at( p, bub ) ) {
            if( !loc || !wants( p, *loc ) ) {
                continue;
            }
            const double v = value( p, *loc );
            if( !best || v > best_value ) {
                best = loc;
                best_value = v;
            }
        }
    }
    return best;
}

item_location best_weapon_in_reach( Character &p )
{
    static std::map<character_id, item_location> best_cache;
    static time_point cached_turn = calendar::before_time_starts;
    static unsigned int cached_generation = 0;
    if( cached_turn != calendar::turn || cached_generation != gear_up_cache_generation ) {
        cached_turn = calendar::turn;
        cached_generation = gear_up_cache_generation;
        best_cache.clear();
    }
    auto it = best_cache.find( p.getID() );
    if( it != best_cache.end() ) {
        return it->second;
    }
    item_location best = best_candidate_in_reach( p, is_weapon_upgrade,
    []( Character & who, const item & itm ) {
        return weapon_score( who, itm );
    } );
    return best_cache.emplace( p.getID(), best ).first->second;
}

// Only the single best weapon anywhere in reach counts as wanted, or the
// character wields whatever mediocre gun the walk happens to reach first and
// never sees the better one sitting on the next shelf.
bool wants_as_weapon( Character &p, const item &it )
{
    return is_weapon_upgrade( p, it ) && best_weapon_in_reach( p ).get_item() == &it;
}

// Nobody who knows what they are doing walks out with a rifle and nothing else.
// Guns jam, run dry, and are useless when something is already on top of you.
bool needs_backup_blade( Character &p )
{
    const double fists = unarmed_score( p );
    item_location wielded = p.get_wielded_item();
    if( wielded && !wielded->is_gun() && weapon_score( p, *wielded, false ) > fists ) {
        return false;
    }
    bool found = false;
    p.visit_items( [&p, &found, fists]( const item * node, item * ) {
        if( is_weapon_candidate( *node ) && !node->is_gun() &&
            weapon_score( p, *node, false ) > fists && p.can_wield( *node ).success() ) {
            found = true;
            return VisitResponse::ABORT;
        }
        return VisitResponse::NEXT;
    } );
    return !found;
}

// A good melee weapon is not a substitute for a gun: reach matters, and a
// blade that outscores every pistol on raw evaluate_weapon still cannot shoot.
// A follower told not to use guns, or to use only silent ones, is not given a
// gun to carry that the orders rule out.
bool orders_rule_out( const Character &p, const item &gun )
{
    const npc *guy = p.as_npc();
    return guy && guy->is_player_ally() &&
           ( !guy->rules.has_flag( ally_rule::use_guns ) ||
             ( guy->rules.has_flag( ally_rule::use_silent ) && !gun.is_silent() ) );
}

// If the camp can feed a gun and the character is not already holding one,
// acquire it as a backup even when the primary weapon is excellent.
bool needs_backup_gun( Character &p )
{
    item_location wielded = p.get_wielded_item();
    if( wielded && wielded->is_gun() ) {
        return false;
    }
    bool has_gun_carried = false;
    p.visit_items( [&has_gun_carried]( const item * node, item * ) {
        if( node->is_gun() ) {
            has_gun_carried = true;
            return VisitResponse::ABORT;
        }
        return VisitResponse::NEXT;
    } );
    return !has_gun_carried;
}

// Everything asked of a backup-blade candidate except whether some other
// tile in reach holds a better one -- see is_weapon_upgrade() for why this
// side must not call wants_as_backup().
bool is_backup_upgrade( Character &p, const item &it )
{
    if( !is_weapon_candidate( it ) || it.is_gun() ||
        p.gear_up_rejected.count( it.typeId() ) > 0 || !p.can_wield( it ).success() ) {
        return false;
    }
    // It has to be carried to be a backup, and can_stash() only asks about
    // volume, so the weight is asked about here.
    if( p.weight_carried() + it.weight() > p.weight_capacity() || !p.can_stash( it ) ) {
        return false;
    }
    return weapon_score( p, it, false ) > unarmed_score( p );
}

item_location best_backup_in_reach( Character &p )
{
    static std::map<character_id, item_location> best_cache;
    static time_point cached_turn = calendar::before_time_starts;
    static unsigned int cached_generation = 0;
    if( cached_turn != calendar::turn || cached_generation != gear_up_cache_generation ) {
        cached_turn = calendar::turn;
        cached_generation = gear_up_cache_generation;
        best_cache.clear();
    }
    auto it = best_cache.find( p.getID() );
    if( it != best_cache.end() ) {
        return it->second;
    }
    item_location best = best_candidate_in_reach( p, is_backup_upgrade,
    []( Character & who, const item & itm ) {
        return weapon_score( who, itm, false );
    } );
    return best_cache.emplace( p.getID(), best ).first->second;
}

// Nothing beats a machete in a crate three tiles away like an umbrella in the
// crate at hand: only the single best backup anywhere in reach is wanted.
bool wants_as_backup( Character &p, const item &it )
{
    return is_backup_upgrade( p, it ) && best_backup_in_reach( p ).get_item() == &it;
}

// The gun counterpart to is_backup_upgrade: carries a gun into inventory as a
// sidearm when the character already holds a melee weapon.  The gun is scored
// with pretend ammo so a shelved empty pistol is still worth carrying -- it
// will be loaded in the supply stage.
bool is_backup_gun_upgrade( Character &p, const item &it )
{
    if( !it.is_gun() || p.gear_up_rejected.count( it.typeId() ) > 0 || orders_rule_out( p, it ) ||
        !p.can_wield( it ).success() ) {
        return false;
    }
    if( !gun_has_ammo_in_reach( p, it ) ) {
        return false;
    }
    if( p.weight_carried() + it.weight() > p.weight_capacity() || !p.can_stash( it ) ) {
        return false;
    }
    return true;
}

item_location best_backup_gun_in_reach( Character &p )
{
    static std::map<character_id, item_location> best_cache;
    static time_point cached_turn = calendar::before_time_starts;
    static unsigned int cached_generation = 0;
    if( cached_turn != calendar::turn || cached_generation != gear_up_cache_generation ) {
        cached_turn = calendar::turn;
        cached_generation = gear_up_cache_generation;
        best_cache.clear();
    }
    auto it = best_cache.find( p.getID() );
    if( it != best_cache.end() ) {
        return it->second;
    }
    item_location best = best_candidate_in_reach( p, is_backup_gun_upgrade,
    []( Character & who, const item & itm ) {
        return weapon_score( who, itm );
    } );
    return best_cache.emplace( p.getID(), best ).first->second;
}

bool wants_as_backup_gun( Character &p, const item &it )
{
    return is_backup_gun_upgrade( p, it ) && best_backup_gun_in_reach( p ).get_item() == &it;
}

// What putting a garment on would take -- the pieces that have to come off
// first -- and what the change is worth, in armour points.
struct garment_plan {
    bool useful = false;
    double gain = 0.0;
    outfit_pieces displaces;
};

// Everything asked of a garment candidate before it is weighed.  Must ask the
// same questions try_one_garment() does, or the character walks to a crate and
// does nothing there, turn after turn.
bool garment_eligible( Character &p, const item &it )
{
    if( it.has_flag( flag_CANT_WEAR ) || hinders_a_fight( it ) ||
        p.gear_up_rejected.count( it.typeId() ) > 0 ) {
        return false;
    }
    if( it.has_flag( flag_SPLINT ) && !splints_a_break( p, it ) ) {
        return false;
    }
    if( overheating_forbids_dressing( p ) || holds_a_favorite( it ) ) {
        return false;
    }
    // Contents stay in the camp, so only what the piece is worn with -- its
    // plates -- is the wearer's to carry.
    return p.weight_carried() + as_worn( p, it ).weight() <= p.weight_capacity();
}

// The best way to put this garment on, if there is one worth doing.  A garment
// that fits straight onto an empty slot is weighed on its own; otherwise it has
// to displace what it shares a patch of skin and a layer with, one piece or all
// of them.  Either way it is the whole outfit that is judged, so that giving up
// a bulky coat for a lighter one is as visible as putting a coat on.
const garment_plan &plan_for( Character &p, const item &it )
{
    static scan_cache<std::pair<character_id, const item *>, garment_plan> cache;
    const std::pair<character_id, const item *> key( p.getID(), &it );
    if( const garment_plan *known = cache.find( key ) ) {
        return *known;
    }
    garment_plan plan;
    if( garment_eligible( p, it ) ) {
        const item &shelf = as_worn( p, it );
        std::vector<outfit_pieces> options;
        // can_wear() only forbids a second rigid piece, so the soft redundancy
        // is asked about separately.
        if( !conflicts_with_worn( p, shelf ) && p.can_wear( it ).success() ) {
            options.emplace_back();
        } else {
            outfit_pieces rivals;
            for( const item *piece : worn_pieces( p ) ) {
                if( !piece->is_favorite && !keeps_the_air_out( *piece ) &&
                    shares_layer_and_sub_part( *piece, shelf ) &&
                    p.can_takeoff( *piece ).success() ) {
                    rivals.push_back( piece );
                    options.push_back( { piece } );
                }
            }
            if( rivals.size() > 1 ) {
                options.push_back( rivals );
            }
        }
        for( const outfit_pieces &option : options ) {
            const double gain = change_gain( p, option, &shelf );
            if( gain > margin_garment && ( !plan.useful || gain > plan.gain ) ) {
                plan.useful = true;
                plan.gain = gain;
                plan.displaces = option;
            }
        }
    }
    return cache.store( key, std::move( plan ) );
}

bool is_garment_upgrade( Character &p, const item &it )
{
    return it.is_armor() && plan_for( p, it ).useful;
}

item_location best_garment_in_reach( Character &p )
{
    static std::map<character_id, item_location> best_cache;
    static time_point cached_turn = calendar::before_time_starts;
    static unsigned int cached_generation = 0;
    if( cached_turn != calendar::turn || cached_generation != gear_up_cache_generation ) {
        cached_turn = calendar::turn;
        cached_generation = gear_up_cache_generation;
        best_cache.clear();
    }
    auto it = best_cache.find( p.getID() );
    if( it != best_cache.end() ) {
        return it->second;
    }
    item_location best = best_candidate_in_reach( p, is_garment_upgrade,
    []( Character & who, const item & itm ) {
        return plan_for( who, itm ).gain;
    } );
    return best_cache.emplace( p.getID(), best ).first->second;
}

// Whatever is worn that costs the fight more in encumbrance than it earns in
// protection, warmth and pockets, and is not worth the trouble to keep.  Only
// bare pieces: a pack with things in it is somebody's kit, not clothing.
const item *best_shed( Character &p )
{
    static scan_cache<character_id, const item *> cache;
    if( const item **known = cache.find( p.getID() ) ) {
        return *known;
    }
    const item *best = nullptr;
    double best_gain = margin_shed;
    // Taking something off can give back no more than is being lost.
    if( standing_of( p ).lost > margin_shed ) {
        for( const item *piece : worn_pieces( p ) ) {
            if( piece->is_favorite || piece->has_flag( flag_INTEGRATED ) ||
                piece->has_flag( flag_SPLINT ) || keeps_the_air_out( *piece ) ||
                holds_loose_items( *piece ) ||
                p.gear_up_rejected.count( piece->typeId() ) > 0 ||
                !p.can_takeoff( *piece ).success() ) {
                continue;
            }
            const double gain = change_gain( p, { piece }, nullptr );
            if( gain > best_gain ) {
                best = piece;
                best_gain = gain;
            }
        }
    }
    return cache.store( p.getID(), best );
}

// Shedding is the last resort: a better garment somewhere in reach would
// replace the burdensome one and keep the coverage.
bool shed_pending( Character &p )
{
    return !best_garment_in_reach( p ) && best_shed( p ) != nullptr;
}

// Where a plate would go and what that is worth.
struct plate_plan {
    bool useful = false;
    double gain = 0.0;
    const item *carrier = nullptr;
};

// The worn carrier as it would be with this plate seated in it, or nothing when
// the engine will not seat it.
const item *seated_copy( const Character &p, const item &carrier, const item &plate )
{
    struct key_type {
        character_id who;
        const item *carrier;
        const item *plate;
        bool operator<( const key_type &rhs ) const {
            return std::tie( who, carrier, plate ) < std::tie( rhs.who, rhs.carrier, rhs.plate );
        }
    };
    static scan_cache<key_type, std::optional<item>> cache;
    const key_type key{ p.getID(), &carrier, &plate };
    std::optional<item> *known = cache.find( key );
    if( !known ) {
        item seated( carrier );
        bool fits = false;
        for( const item_pocket *pocket : seated.get_ablative_pockets() ) {
            fits = fits || ( pocket->empty() && pocket->can_contain( plate ).success() );
        }
        fits = fits &&
               seated.put_in( plate, pocket_type::CONTAINER, false, nullptr, true ).success();
        std::optional<item> result;
        if( fits ) {
            result = std::move( seated );
        }
        known = &cache.store( key, std::move( result ) );
    }
    return known->has_value() ? &known->value() : nullptr;
}

const plate_plan &plate_plan_for( Character &p, const item &plate )
{
    static scan_cache<std::pair<character_id, const item *>, plate_plan> cache;
    const std::pair<character_id, const item *> key( p.getID(), &plate );
    if( const plate_plan *known = cache.find( key ) ) {
        return *known;
    }
    plate_plan plan;
    if( is_plate( plate ) && p.gear_up_rejected.count( plate.typeId() ) == 0 &&
        p.weight_carried() + plate.weight() <= p.weight_capacity() ) {
        for( const item *carrier : worn_pieces( p ) ) {
            const item *seated = carrier->is_ablative() ? seated_copy( p, *carrier, plate ) :
                                 nullptr;
            if( !seated ) {
                continue;
            }
            const double gain = change_gain( p, { carrier }, seated );
            if( gain > margin_garment && ( !plan.useful || gain > plan.gain ) ) {
                plan.useful = true;
                plan.gain = gain;
                plan.carrier = carrier;
            }
        }
    }
    return cache.store( key, plan );
}

item_location best_plate_in_reach( Character &p )
{
    static std::map<character_id, item_location> best_cache;
    static time_point cached_turn = calendar::before_time_starts;
    static unsigned int cached_generation = 0;
    if( cached_turn != calendar::turn || cached_generation != gear_up_cache_generation ) {
        cached_turn = calendar::turn;
        cached_generation = gear_up_cache_generation;
        best_cache.clear();
    }
    auto it = best_cache.find( p.getID() );
    if( it != best_cache.end() ) {
        return it->second;
    }
    item_location best = best_candidate_in_reach( p, []( Character & who, const item & itm ) {
        return plate_plan_for( who, itm ).useful;
    },
    []( Character & who, const item & itm ) {
        return plate_plan_for( who, itm ).gain;
    } );
    return best_cache.emplace( p.getID(), best ).first->second;
}

bool wants_as_plate( Character &p, const item &it )
{
    return is_plate( it ) && plate_plan_for( p, it ).useful &&
           best_plate_in_reach( p ).get_item() == &it;
}

bool needs_storage( const Character &p )
{
    return units::to_liter( p.volume_capacity( carries_things ) ) < want_storage_liters_floor;
}

item_location best_storage_in_reach( Character &p )
{
    static std::map<character_id, item_location> best_cache;
    static time_point cached_turn = calendar::before_time_starts;
    static unsigned int cached_generation = 0;
    if( cached_turn != calendar::turn || cached_generation != gear_up_cache_generation ) {
        cached_turn = calendar::turn;
        cached_generation = gear_up_cache_generation;
        best_cache.clear();
    }
    auto it = best_cache.find( p.getID() );
    if( it != best_cache.end() ) {
        return it->second;
    }
    item_location best = best_candidate_in_reach( p, []( Character & who, const item & itm ) {
        return itm.get_volume_capacity( carries_things ) > 0_ml && is_garment_upgrade( who, itm );
    },
    []( Character &, const item & itm ) {
        // Ranked on the room it offers, not on wear_proxy(): this search runs
        // only while there is nowhere to put anything, and a coat that scores
        // well on armour is not the answer to that.  Everything the supply
        // stage does, and carrying a backup blade at all, waits on pockets.
        return units::to_liter( itm.get_volume_capacity( carries_things ) );
    } );
    return best_cache.emplace( p.getID(), best ).first->second;
}

// Only the single best garment anywhere in reach counts as wanted: comparing
// only what one tile happens to offer against whatever is already worn is how
// a character ends up trying on and shedding half the camp's wardrobe walking
// past crate after crate, never seeing that a better piece was two tiles back.
// Processed one at a time in strictly improving order this way, several
// non-conflicting pieces still end up worn -- each pass finds whatever is now
// the single best remaining upgrade, worn or not, anywhere in reach.  While
// storage is critically low, the search narrows to pocket-bearing candidates
// only, unless the camp genuinely has none to offer.
bool worth_trying_on( Character &p, const item &it )
{
    if( needs_storage( p ) ) {
        item_location storage_pick = best_storage_in_reach( p );
        if( storage_pick ) {
            return storage_pick.get_item() == &it && is_garment_upgrade( p, it );
        }
    }
    return is_garment_upgrade( p, it ) && best_garment_in_reach( p ).get_item() == &it;
}

bool wants_magazine( Character &p, const item &it )
{
    item_location wielded = p.get_wielded_item();
    if( !wielded || !wielded->is_gun() || wielded->magazine_integral() || !it.is_magazine() ) {
        return false;
    }
    const std::set<itype_id> compatible = wielded->magazine_compatible();
    if( compatible.count( it.typeId() ) == 0 ) {
        return false;
    }
    const int have = count_carried( p, [&compatible]( const item & carried ) {
        return carried.is_magazine() && compatible.count( carried.typeId() ) > 0;
    } );
    return have < want_spare_magazines;
}

int ammo_shortfall( Character &p )
{
    item_location wielded = p.get_wielded_item();
    if( !wielded || !wielded->is_gun() ) {
        return 0;
    }
    const std::set<ammotype> types = wielded->ammo_types();
    if( types.empty() ) {
        return 0;
    }
    // An empty magazine-fed gun reports no capacity of its own, so take the
    // figure from a magazine actually being carried.
    int capacity = wielded->ammo_capacity( *types.begin() );
    if( capacity <= 0 && !wielded->magazine_integral() ) {
        const std::set<itype_id> compatible = wielded->magazine_compatible();
        p.visit_items( [&capacity, &types, &compatible]( const item * node, item * ) {
            if( node->is_magazine() && compatible.count( node->typeId() ) > 0 ) {
                capacity = std::max( capacity, node->ammo_capacity( *types.begin() ) );
            }
            return VisitResponse::NEXT;
        } );
    }
    capacity = std::max( 1, capacity );
    const int have = count_ammo_carried( p, types );
    return std::max( 0, capacity * want_ammo_loads - have );
}

// What one round of this does when it lands: every projectile in it, with
// armour piercing counting for a little more than its damage.
double ammo_punch( const item &it )
{
    if( !it.is_ammo() || !it.type->ammo ) {
        return 0.0;
    }
    const islot_ammo &round = *it.type->ammo;
    const bool shot = round.count > 1 && !round.shot_damage.empty();
    double punch = 0.0;
    for( const damage_unit &unit : ( shot ? round.shot_damage : round.damage ).damage_units ) {
        punch += unit.amount * ( 1.0 + 0.05 * unit.res_pen );
    }
    return punch * std::max( 1, round.count );
}

bool wants_ammo( Character &p, const item &it )
{
    if( !it.is_ammo() ) {
        return false;
    }
    item_location wielded = p.get_wielded_item();
    if( !wielded || !wielded->is_gun() ) {
        return false;
    }
    return wielded->ammo_types().count( it.ammo_type() ) > 0 && ammo_shortfall( p ) > 0;
}

bool wants_medical( Character &p, const item &it )
{
    if( is_healing_item( it ) ) {
        return count_carried( p, is_healing_item ) < want_healing_items;
    }
    if( is_painkiller( it ) ) {
        return count_carried( p, is_painkiller ) < want_painkillers;
    }
    return false;
}

// The NPC combat AI decides what it is willing to throw in
// npc_attack_throw::can_use(); stocking anything it would refuse to throw is
// dead weight.  NPC_THROWN is the hand-picked side of that test, so it is what
// gets stocked -- thrown_damage cannot be one, since item_factory hands every
// item in the game a share of its bash damage as a throwing value.  Items
// flagged NPC_THROW_NOW arrive carrying NPC_THROWN too but mean the opposite
// thing: a lit stick of dynamite is something to be rid of, not to stock.
bool is_thrown_candidate( const item &it )
{
    return it.has_flag( flag_NPC_THROWN ) && !it.has_flag( flag_NPC_THROW_NOW ) &&
           !it.has_flag( flag_NPC_ACTIVATE ) && !it.is_gun() && !it.is_armor() &&
           !it.is_comestible() && !it.is_magazine() && !it.is_tool();
}

// What the character could actually throw right now.  The weapon in hand does
// not count: npc_attack_throw::evaluate() refuses to throw the best weapon it
// has when no second copy exists, so a lone wielded javelin is a spear, not a
// throwing stock.
void carried_thrown( const Character &who, units::volume &volume, units::mass &weight )
{
    volume = 0_ml;
    weight = 0_gram;
    item_location wielded = who.get_wielded_item();
    const item *in_hand = wielded ? &*wielded : nullptr;
    who.visit_items( [&volume, &weight, in_hand]( const item * node, item * ) {
        if( !is_thrown_candidate( *node ) ) {
            return VisitResponse::NEXT;
        }
        const int stack = std::max( 1, node->count() );
        const int usable = node == in_hand ? stack - 1 : stack;
        if( usable > 0 ) {
            volume += node->volume() / stack * usable;
            weight += node->weight() / stack * usable;
        }
        return VisitResponse::NEXT;
    } );
}

// How much of this stack the budget still has room for.  A javelin costs a
// liter apiece and a rock a quarter of one, so one budget buys a single
// javelin or a handful of rocks without either being counted out by hand, and
// a mixed haul falls out of the same arithmetic.
int thrown_wanted( Character &p, const item &it )
{
    if( !is_thrown_candidate( it ) || p.gear_up_rejected.count( it.typeId() ) > 0 ) {
        return 0;
    }
    units::volume carried_volume;
    units::mass carried_weight;
    carried_thrown( p, carried_volume, carried_weight );
    const int stack = std::max( 1, it.count() );
    const units::volume each_volume = std::max( 1_ml, it.volume() / stack );
    const units::mass each_weight = std::max( 1_gram, it.weight() / stack );
    const int by_volume = ( want_thrown_volume - carried_volume ) / each_volume;
    const int by_weight = ( want_thrown_weight - carried_weight ) / each_weight;
    return std::max( 0, std::min( { by_volume, by_weight, want_thrown_per_stack } ) );
}

bool wants_thrown( Character &p, const item &it )
{
    return thrown_wanted( p, it ) > 0;
}

void carried_nutrition( const Character &who, int &kcal, int &quench )
{
    kcal = 0;
    quench = 0;
    who.visit_items( [&kcal, &quench]( const item * node, item * ) {
        if( node->is_food() ) {
            const auto &carried = node->get_comestible();
            if( carried ) {
                kcal += carried->default_nutrition_read_only().kcal() * node->count();
                quench += carried->quench * node->count();
            }
        }
        return VisitResponse::NEXT;
    } );
}

// With the NPC needs mod active NPCs neither eat nor drink, so handing them
// rations would be pure clutter.  needs_food() is the same gate the behaviour
// tree uses, so this stays aligned with the mod rather than fighting it.
bool wants_rations( Character &p, const item &it )
{
    if( !p.needs_food() || !it.is_food() ) {
        return false;
    }
    const auto &com = it.get_comestible();
    if( !com || !p.will_eat( it ).success() ) {
        return false;
    }
    int kcal = 0;
    int quench = 0;
    carried_nutrition( p, kcal, quench );
    if( kcal < want_kcal && com->default_nutrition_read_only().kcal() > 0 ) {
        return true;
    }
    return quench < want_quench && com->quench > 0;
}

// Everything in it is something worth drinking: taking a vessel means taking
// all of it, so a jug of water counts and a toolbox with a bottle rattling
// around in it does not.
bool holds_only_drink( Character &p, const item &it )
{
    if( it.is_food() || it.made_of( phase_id::LIQUID ) ) {
        return false;
    }
    const std::list<const item *> contents = it.all_items_top( pocket_type::CONTAINER );
    if( contents.empty() ) {
        return false;
    }
    for( const item *inner : contents ) {
        if( inner->is_favorite || !inner->is_food() ) {
            return false;
        }
        const auto &com = inner->get_comestible();
        if( !com || com->quench <= 0 || !p.will_eat( *inner ).success() ) {
            return false;
        }
    }
    return true;
}

// Loose liquid cannot be carried, and a camp keeps its water in canteens and
// jugs, so the drink has to be taken by the vessel holding it.  Bounded by the
// count as well as by the target: a camp keeping its water in twenty small
// bottles should not be stripped of all twenty.
bool wants_as_drink( Character &p, const item &it )
{
    if( !p.needs_food() || !holds_only_drink( p, it ) ) {
        return false;
    }
    int kcal = 0;
    int quench = 0;
    carried_nutrition( p, kcal, quench );
    if( quench >= want_quench ) {
        return false;
    }
    const int have = count_carried( p, [&p]( const item & carried ) {
        return holds_only_drink( p, carried );
    } );
    return have < want_drink_vessels;
}

// How many of this ration close the gap to the food and water targets.  The
// whole stack would be the camp's larder, not one fighter's day.
int rations_wanted( const Character &p, const item &it )
{
    const auto &com = it.get_comestible();
    if( !com ) {
        return 0;
    }
    int kcal = 0;
    int quench = 0;
    carried_nutrition( p, kcal, quench );
    int want = 0;
    const int per_kcal = com->default_nutrition_read_only().kcal();
    if( per_kcal > 0 && kcal < want_kcal ) {
        want = ( want_kcal - kcal + per_kcal - 1 ) / per_kcal;
    }
    if( com->quench > 0 && quench < want_quench ) {
        want = std::max( want, ( want_quench - quench + com->quench - 1 ) / com->quench );
    }
    return want;
}

bool wanted_for_stage( Character &p, const item &it, gear_stage stage )
{
    if( stage == gear_stage::equipment ) {
        // needs_backup_blade() first: it only walks carried gear, where
        // wants_as_backup() scans every store tile in reach for the best
        // candidate, and this runs for every item in the camp.
        return wants_as_weapon( p, it ) ||
               ( needs_backup_blade( p ) && wants_as_backup( p, it ) ) ||
               ( needs_backup_gun( p ) && wants_as_backup_gun( p, it ) ) ||
               worth_trying_on( p, it ) || wants_as_plate( p, it );
    }
    // A supply that could not be carried (no room, too heavy) never stops
    // being wanted on its own; only this memory ends the sweep.
    if( p.gear_up_rejected.count( it.typeId() ) > 0 ) {
        return false;
    }
    return wants_magazine( p, it ) || wants_ammo( p, it ) ||
           wants_medical( p, it ) || wants_rations( p, it ) || wants_as_drink( p, it ) ||
           wants_thrown( p, it );
}

// Mirrors collect_from()'s descent exactly, including where it stops: a want
// seen deeper than the pool ever reaches would be a tile walked to and nothing
// done there, every turn, forever.
bool pile_has_anything_wanted( Character &p, const item &it, gear_stage stage, int depth )
{
    if( wanted_for_stage( p, it, stage ) ) {
        return true;
    }
    if( depth > max_nesting_depth ) {
        return false;
    }
    const std::vector<const item *> plates = plates_in( it );
    for( const item *inner : it.all_items_top( pocket_type::CONTAINER ) ) {
        if( !off_limits_item( p, *inner ) &&
            std::find( plates.begin(), plates.end(), inner ) == plates.end() &&
            pile_has_anything_wanted( p, *inner, stage, depth + 1 ) ) {
            return true;
        }
    }
    return false;
}

// Cheap tile test for "is this worth walking to".  Bails on the first hit
// rather than building and sorting a pool: with nesting, one storage tile can
// expose hundreds of items, and this runs for every location every turn.
bool tile_has_anything_wanted( Character &p, const tripoint_bub_ms &tile, gear_stage stage )
{
    map &here = get_map();
    if( !here.inbounds( tile ) || tile_is_off_limits( p, tile ) ) {
        return false;
    }
    // Taking something off needs nothing from the tile but somewhere to put it.
    if( stage == gear_stage::equipment && shed_pending( p ) ) {
        return true;
    }
    // Both the places candidates_at() draws from, or the sweep walks to a
    // trunk it has already decided is worth visiting and finds nothing there.
    if( const std::optional<vpart_reference> vp = here.veh_at( tile ).cargo() ) {
        for( item &it : vp->items() ) {
            if( !off_limits_item( p, it ) && pile_has_anything_wanted( p, it, stage, 1 ) ) {
                return true;
            }
        }
    }
    for( item &it : here.i_at( tile ) ) {
        if( !off_limits_item( p, it ) && pile_has_anything_wanted( p, it, stage, 1 ) ) {
            return true;
        }
    }
    return false;
}

// ---------------------------------------------------------------------------
// Acting on one tile
// ---------------------------------------------------------------------------

// Putting on a sports bag and inheriting seventy-six shirts is not gearing up:
// the contents go back into the camp's zones, not onto someone's back.
void empty_where_it_stands( Character &who, item_location &loc, const tripoint_bub_ms &tile )
{
    const std::list<item *> contents = loc->all_items_top( pocket_type::CONTAINER );
    const std::vector<const item *> plates = plates_in( *loc );
    int moved = 0;
    for( item *inner : contents ) {
        if( std::find( plates.begin(), plates.end(), inner ) != plates.end() ) {
            continue;
        }
        const item copy = *inner;
        if( !put_away( who, copy, tile ) ) {
            continue;
        }
        loc->remove_item( *inner );
        moved++;
    }
    if( moved > 0 ) {
        who.mod_moves( -moved * handle_cost_moves );
    }
}

// What was in the old pack goes into the new one, and what will not fit goes
// into storage.  A swapped-out pack is never discarded with its contents in it.
void transfer_contents( Character &who, item &from, item &to, const tripoint_bub_ms &tile )
{
    const std::list<item *> contents = from.all_items_top( pocket_type::CONTAINER );
    for( item *inner : contents ) {
        const item copy = *inner;
        // Insert first, remove second, and let the insert itself decide:
        // can_contain() will pass a pocket that put_in() then refuses -- over
        // liquids, over length -- and taking the item out of the old pack
        // before finding that out destroys it.  Asked quietly because a
        // refusal here is an ordinary answer, not a fault.
        if( to.put_in( copy, pocket_type::CONTAINER, false, nullptr, true ).success() ) {
            from.remove_item( *inner );
            who.mod_moves( -handle_cost_moves );
            continue;
        }
        if( who.can_stash( copy ) && who.i_add( copy ) ) {
            from.remove_item( *inner );
            who.mod_moves( -handle_cost_moves );
            continue;
        }
        if( put_away( who, copy, tile ) ) {
            from.remove_item( *inner );
            who.mod_moves( -handle_cost_moves );
        }
    }
}

item_location worn_location( Character &p, const item *piece )
{
    for( item_location &loc : p.all_items_loc() ) {
        if( loc && loc.get_item() == piece ) {
            return loc;
        }
    }
    return {};
}

// Back where it was, or failing that in the camp's storage and failing that on
// the crate: it exists only in the takeoff list here, so anything less loses it.
void put_back_on( Character &p, item &piece, const tripoint_bub_ms &tile )
{
    if( !p.wear_item( piece, false, true, true, true ) && !put_away( p, piece, tile ) ) {
        place_at( tile, piece );
    }
}

// Puts on the garment the plan chose, taking off what the plan displaces.
// What physically fits -- pocket length, body size, rigid conflicts, power
// armour -- stays the engine's call: anything it refuses is put back as it was.
// Returns true if something changed.
bool try_one_garment( Character &p, item_location &loc, const tripoint_bub_ms &tile )
{
    const itype_id candidate_type = loc->typeId();
    const garment_plan plan = plan_for( p, *loc );
    if( !plan.useful ) {
        p.gear_up_rejected.insert( candidate_type );
        return false;
    }
    p.mod_moves( -p.item_wear_cost( *loc ) );

    if( plan.displaces.empty() ) {
        empty_where_it_stands( p, loc, tile );
        // Weighed again on what is left: a camp with nowhere to put the
        // contents hands over a bag that is still full, and that weight is
        // the wearer's problem, not the estimate's.
        if( !loc || p.weight_carried() + loc->weight() > p.weight_capacity() ) {
            p.gear_up_rejected.insert( candidate_type );
            return false;
        }
        const item candidate = *loc;
        std::optional<std::list<item>::iterator> worn_it =
            p.wear_item( candidate, false, true, true, true );
        if( worn_it ) {
            loc.remove_item();
            p.add_msg_player_or_npc( m_good, _( "You put on the %s." ),
                                     _( "<npcname> puts on a %s." ), candidate.tname() );
            return true;
        }
        p.gear_up_rejected.insert( candidate_type );
        return false;
    }

    // The old pieces come off first: two rigid pieces cannot share a sub-part
    // even for a moment, so wearing the new one first would quietly veto every
    // helmet-for-helmet upgrade.  They keep their contents while they wait in
    // the takeoff lists, so nothing is homeless in between.
    std::vector<std::list<item>> removed( plan.displaces.size() );
    std::vector<std::string> names;
    size_t taken_off = 0;
    for( const item *piece : plan.displaces ) {
        item_location worn = worn_location( p, piece );
        if( !worn ) {
            break;
        }
        names.push_back( worn->tname() );
        if( !quiet_takeoff( p, worn, removed[taken_off] ) || removed[taken_off].empty() ) {
            break;
        }
        taken_off++;
    }
    const auto restore_all = [&]() {
        for( size_t i = taken_off; i-- > 0; ) {
            for( item &piece : removed[i] ) {
                put_back_on( p, piece, tile );
            }
        }
        p.gear_up_rejected.insert( candidate_type );
    };
    if( taken_off < plan.displaces.size() ) {
        restore_all();
        return false;
    }

    // Only now is the candidate emptied.  Everything that could still turn this
    // swap down has been asked.
    empty_where_it_stands( p, loc, tile );

    std::optional<std::list<item>::iterator> worn_it;
    if( loc && p.weight_carried() + loc->weight() <= p.weight_capacity() ) {
        worn_it = p.wear_item( *loc, false, true, true, true );
    }
    if( !worn_it ) {
        // The new one would not go on after all, so the old ones go straight
        // back on, contents untouched.
        restore_all();
        return false;
    }
    const item candidate = **worn_it;
    for( std::list<item> &pieces : removed ) {
        for( item &old_worn : pieces ) {
            transfer_contents( p, old_worn, **worn_it, tile );
        }
    }

    loc.remove_item();
    for( std::list<item> &pieces : removed ) {
        for( item &old_worn : pieces ) {
            // The swap moved the totals the outfit is scored against, so the
            // displaced piece can look attractive again and trade places with
            // its replacement forever without this.
            p.gear_up_rejected.insert( old_worn.typeId() );
            // Back into its zone, and failing that down on the crate it was
            // traded at.
            if( !put_away( p, old_worn, tile ) ) {
                place_at( tile, old_worn );
            }
        }
    }
    p.add_msg_player_or_npc( m_good, _( "You swap your %1$s for the %2$s." ),
                             _( "<npcname> swaps their %1$s for a %2$s." ),
                             names.front(), candidate.tname() );
    for( size_t i = 1; i < names.size(); i++ ) {
        p.add_msg_player_or_npc( m_good, _( "You take off your %s." ),
                                 _( "<npcname> takes off their %s." ), names[i] );
    }
    return true;
}

// Slides a plate into the carrier the plan chose.
bool seat_one_plate( Character &p, item_location &loc )
{
    const itype_id plate_type = loc->typeId();
    const plate_plan plan = plate_plan_for( p, *loc );
    item_location carrier = plan.useful ? worn_location( p, plan.carrier ) : item_location();
    if( !carrier ) {
        p.gear_up_rejected.insert( plate_type );
        return false;
    }
    const std::string plate_name = loc->type_name();
    const std::string carrier_name = carrier->type_name();
    if( !carrier->put_in( *loc, pocket_type::CONTAINER, false, nullptr, true ).success() ) {
        p.gear_up_rejected.insert( plate_type );
        return false;
    }
    loc.remove_item();
    p.mod_moves( -handle_cost_moves );
    p.worn.recalc_ablative_blocking( &p );
    p.calc_encumbrance();
    p.add_msg_player_or_npc( m_good, _( "You slide the %1$s into your %2$s." ),
                             _( "<npcname> slides a %1$s into their %2$s." ), plate_name,
                             carrier_name );
    return true;
}

// Takes one worn piece off and puts it away.  It is remembered as turned down
// first, so that however it ends the order does not put it back on.
bool shed_one( Character &p, const item *piece, const tripoint_bub_ms &tile )
{
    item_location worn = worn_location( p, piece );
    if( !worn ) {
        return true;
    }
    const std::string name = worn->tname();
    p.gear_up_rejected.insert( worn->typeId() );
    std::list<item> removed;
    if( !quiet_takeoff( p, worn, removed ) || removed.empty() ) {
        return true;
    }
    p.mod_moves( -p.item_wear_cost( removed.front() ) );
    for( item &old_worn : removed ) {
        if( !put_away( p, old_worn, tile ) ) {
            place_at( tile, old_worn );
        }
    }
    p.add_msg_player_or_npc( m_good, _( "You take off your %s; it costs more than it protects." ),
                             _( "<npcname> takes off their %s; it costs more than it protects." ),
                             name );
    return true;
}

bool do_equipment_stage( Character &p, const tripoint_bub_ms &tile )
{
    std::vector<item_location> pool = candidates_at( p, tile );

    // Weapon first: the weapon decides which ammunition is coherent later.
    // At most one entry in this tile's pool can be the camp's single best
    // weapon, wants_as_weapon() having already ruled out every runner-up.
    item_location best;
    for( item_location &loc : pool ) {
        if( loc && wants_as_weapon( p, *loc ) ) {
            best = loc;
            break;
        }
    }
    if( best ) {
        const std::string taken = best->tname();
        const itype_id taken_type = best->typeId();
        item_location wielded = p.get_wielded_item();
        if( wielded ) {
            const item old = *wielded;
            if( !p.can_unwield( old ).success() ) {
                // The candidate can never be taken while the hands are stuck,
                // so remember it or this repeats every turn.
                p.gear_up_rejected.insert( taken_type );
                p.add_msg_player_or_npc( m_warning, _( "You can't let go of your %s." ),
                                         _( "<npcname> can't let go of their %s." ), old.tname() );
                return true;
            }
            // Empty the hands here: the wield path is allowed to stow the old
            // weapon anywhere, up to and including the ground under it.  Into
            // storage, and failing that down on the crate being traded at.
            item removed = p.remove_weapon();
            if( !put_away( p, removed, tile ) ) {
                place_at( tile, removed );
            }
            if( !wield_loc( p, best ) ) {
                // Hands are empty and the new weapon would not come: take the
                // old one back rather than walk away unarmed.
                p.gear_up_rejected.insert( taken_type );
                item_location recovered = find_carried( p, old.typeId() );
                if( recovered ) {
                    wield_loc( p, recovered );
                }
                return true;
            }
            // The old weapon is not blacklisted here: weapon_score() scores a
            // wielded item and a shelved one on identical, uncached terms, so a
            // strictly worse weapon stays strictly worse and cannot trade places
            // with its replacement.  Blacklisting it would only cost the one
            // role gear_up_rejected does not distinguish -- the same item as a
            // candidate backup blade, back on a store tile where it belongs.
        } else if( !wield_loc( p, best ) ) {
            p.gear_up_rejected.insert( taken_type );
            return true;
        }
        // npc::wield announces itself; only the avatar's side needs saying.
        p.add_msg_if_player( m_good, _( "You take up the %s." ), taken );
        return true;
    }

    if( needs_backup_blade( p ) ) {
        // Same reasoning as the weapon above: at most one entry here can be
        // the camp's single best backup blade.
        item_location blade;
        for( item_location &loc : pool ) {
            if( loc && wants_as_backup( p, *loc ) ) {
                blade = loc;
                break;
            }
        }
        if( blade ) {
            const std::string taken = blade->tname();
            const itype_id blade_type = blade->typeId();
            if( take_into_inventory( p, blade ) ) {
                p.add_msg_player_or_npc( m_good, _( "You take the %s as a backup." ),
                                         _( "<npcname> takes a %s as a backup." ), taken );
                return true;
            }
            p.gear_up_rejected.insert( blade_type );
        }
    }

    if( needs_backup_gun( p ) ) {
        item_location gun;
        for( item_location &loc : pool ) {
            if( loc && wants_as_backup_gun( p, *loc ) ) {
                gun = loc;
                break;
            }
        }
        if( gun ) {
            const std::string taken = gun->tname();
            const itype_id gun_type = gun->typeId();
            if( take_into_inventory( p, gun ) ) {
                p.add_msg_player_or_npc( m_good, _( "You take the %s as a sidearm." ),
                                         _( "<npcname> takes a %s as a sidearm." ), taken );
                return true;
            }
            p.gear_up_rejected.insert( gun_type );
        }
    }

    // Then clothing: at most one entry in this tile's pool can be the single
    // best garment anywhere in reach, worth_trying_on() having already ruled
    // out every runner-up.  Nothing to sort between candidates that compete
    // with each other any more -- only whether the winner happens to be here.
    for( item_location &loc : pool ) {
        if( loc && worth_trying_on( p, *loc ) ) {
            return try_one_garment( p, loc, tile );
        }
    }
    for( item_location &loc : pool ) {
        if( loc && wants_as_plate( p, *loc ) ) {
            return seat_one_plate( p, loc );
        }
    }
    if( shed_pending( p ) ) {
        return shed_one( p, best_shed( p ), tile );
    }
    return false;
}

bool do_supply_stage( Character &p, const tripoint_bub_ms &tile )
{
    std::vector<item_location> pool = candidates_at( p, tile );
    bool did_something = false;

    for( item_location &loc : pool ) {
        if( !loc || !wants_magazine( p, *loc ) ) {
            continue;
        }
        const std::string name = loc->tname();
        const itype_id type = loc->typeId();
        if( take_into_inventory( p, loc ) ) {
            p.add_msg_player_or_npc( m_good, _( "You pick up the %s." ),
                                     _( "<npcname> picks up a %s." ), name );
            did_something = true;
        } else {
            p.gear_up_rejected.insert( type );
        }
    }

    // The shortfall is met from the hardest-hitting stack first, not from whichever
    // happens to lie on top of the crate.
    std::vector<item_location *> by_punch;
    for( item_location &loc : pool ) {
        by_punch.push_back( &loc );
    }
    std::stable_sort( by_punch.begin(), by_punch.end(),
    []( const item_location * a, const item_location * b ) {
        return *a && *b && ammo_punch( **a ) > ammo_punch( **b );
    } );
    int taken = 0;
    for( item_location *entry : by_punch ) {
        item_location &loc = *entry;
        const int want = ammo_shortfall( p );
        if( want <= 0 ) {
            break;
        }
        if( !loc || !wants_ammo( p, *loc ) ) {
            continue;
        }
        const itype_id type = loc->typeId();
        const int got = take_charges( p, loc, want );
        if( got > 0 ) {
            taken += got;
        } else {
            p.gear_up_rejected.insert( type );
        }
    }
    if( taken > 0 ) {
        p.add_msg_player_or_npc( m_good, n_gettext( "You take %d round of ammunition.",
                                 "You take %d rounds of ammunition.", taken ),
                                 n_gettext( "<npcname> takes %d round of ammunition.",
                                            "<npcname> takes %d rounds of ammunition.", taken ), taken );
        did_something = true;
    }

    for( item_location &loc : pool ) {
        if( !loc || !wants_medical( p, *loc ) ) {
            continue;
        }
        const bool healing = is_healing_item( *loc );
        const int want = healing
                         ? want_healing_items - count_carried( p, is_healing_item )
                         : want_painkillers - count_carried( p, is_painkiller );
        const std::string name = loc->tname();
        const itype_id type = loc->typeId();
        if( take_charges( p, loc, want ) > 0 ) {
            p.add_msg_player_or_npc( m_good, _( "You take the %s." ),
                                     _( "<npcname> takes a %s." ), name );
            did_something = true;
        } else {
            p.gear_up_rejected.insert( type );
        }
    }

    for( item_location &loc : pool ) {
        if( !loc || !wants_rations( p, *loc ) ) {
            continue;
        }
        // A day's food, not the camp's larder: take only what closes the gap.
        const int want = rations_wanted( p, *loc );
        const std::string name = loc->tname();
        const itype_id type = loc->typeId();
        if( want > 0 && take_charges( p, loc, want ) > 0 ) {
            p.add_msg_player_or_npc( m_good, _( "You pack the %s." ),
                                     _( "<npcname> packs a %s." ), name );
            did_something = true;
        } else {
            p.gear_up_rejected.insert( type );
        }
    }

    // Something to throw when the gun runs dry and the horde has not.  Stacks
    // that count by charges come off a tile in one go; the rest are one item
    // per location, so the same tile is walked more than once.
    int thrown_taken = 0;
    for( item_location &loc : pool ) {
        if( !loc || !wants_thrown( p, *loc ) ) {
            continue;
        }
        const int want = thrown_wanted( p, *loc );
        const itype_id type = loc->typeId();
        const int got = take_charges( p, loc, want );
        if( got > 0 ) {
            thrown_taken += got;
        } else {
            p.gear_up_rejected.insert( type );
        }
    }
    if( thrown_taken > 0 ) {
        p.add_msg_player_or_npc( m_good, n_gettext( "You pack %d throwable.",
                                 "You pack %d throwables.", thrown_taken ),
                                 n_gettext( "<npcname> packs %d throwable.",
                                            "<npcname> packs %d throwables.", thrown_taken ), thrown_taken );
        did_something = true;
    }

    // Water comes by the canteen, so the whole vessel goes along.
    for( item_location &loc : pool ) {
        if( !loc || !wants_as_drink( p, *loc ) ) {
            continue;
        }
        const std::string name = loc->tname();
        const itype_id type = loc->typeId();
        if( take_into_inventory( p, loc ) ) {
            p.add_msg_player_or_npc( m_good, _( "You pack the %s." ),
                                     _( "<npcname> packs a %s." ), name );
            did_something = true;
        } else {
            p.gear_up_rejected.insert( type );
        }
    }

    // Walk into the fight with a full magazine, not just a full pocket.  Two
    // steps, because a magazine-fed weapon needs both: loose rounds go into the
    // magazines first, and only then does a loaded magazine go into the gun.
    item_location wielded = p.get_wielded_item();
    if( wielded && wielded->is_gun() ) {
        if( !wielded->magazine_integral() ) {
            const std::set<itype_id> compatible = wielded->magazine_compatible();
            for( item_location &carried : p.all_items_loc() ) {
                if( !carried || !carried->is_magazine() ||
                    compatible.count( carried->typeId() ) == 0 || carried->is_magazine_full() ) {
                    continue;
                }
                if( try_reload( p, carried ) ) {
                    did_something = true;
                }
            }
        }
        item_location to_load = p.get_wielded_item();
        if( to_load && try_reload( p, to_load ) ) {
            did_something = true;
        }
    }

    return did_something;
}

} // namespace

// ---------------------------------------------------------------------------
// The activity
// ---------------------------------------------------------------------------

namespace
{

// Every store tile that still offers something for the given stage.  No
// pruning: callers that route a character there prune, callers that only ask
// "is this stage finished" must not, or a dark corner would read as done.
std::unordered_set<tripoint_abs_ms> tiles_wanted_for( Character &you, gear_stage stage )
{
    map &here = get_map();
    std::unordered_set<tripoint_abs_ms> wanted;
    for( const tripoint_abs_ms &tile : stores_within_reach( you ) ) {
        const tripoint_bub_ms bub = here.get_bub( tile );
        if( !here.inbounds( bub ) ) {
            // Outside the reality bubble; let the framework route there and
            // decide once it can actually see the tile.
            wanted.emplace( tile );
            continue;
        }
        if( tile_has_anything_wanted( you, bub, stage ) ) {
            wanted.emplace( tile );
        }
    }
    return wanted;
}

void report_gear_up_finished( Character &you )
{
    if( you.gear_up_done_reported ) {
        return;
    }
    you.gear_up_done_reported = true;
    if( npc *p = you.as_npc() ) {
        // Unconditional, unlike add_msg_player_or_npc: whether an order the
        // player gave is finished is worth knowing off-screen too, not only
        // at the moment the player happens to be looking at whoever got it.
        p->add_msg_if_npc( m_good, _( "<npcname> finishes gearing up from the stores." ) );
    } else {
        you.add_msg_if_player( m_good, _( "You finish gearing up from the stores." ) );
    }
}

} // namespace

std::unordered_set<tripoint_abs_ms> multi_gear_up_activity_actor::multi_activity_locations(
    Character &you )
{
    // Ammunition is only coherent once the weapon is final, so the equipment
    // stage has to be exhausted everywhere before the supply stage can begin.
    std::unordered_set<tripoint_abs_ms> wanted =
        tiles_wanted_for( you, static_cast<gear_stage>( you.gear_up_stage ) );
    if( wanted.empty() && you.gear_up_stage == static_cast<int>( gear_stage::equipment ) ) {
        you.gear_up_stage = static_cast<int>( gear_stage::supplies );
        wanted = tiles_wanted_for( you, gear_stage::supplies );
    }

    // Empty before pruning means finished; empty after it could just be a
    // dangerous field this turn.  The distinction has to be taken here.
    const bool order_complete =
        wanted.empty() && you.gear_up_stage == static_cast<int>( gear_stage::supplies );
    multi_activity_actor::prune_dangerous_field_locations( wanted );
    multi_activity_actor::prune_same_tile_locations( you, wanted );
    // Guarded the way generic_locations guards it.  A camp's store room is
    // usually windowless and loot sorting is allowed there, so this is too.
    if( !multi_activity_actor::can_do_in_dark( get_type() ) ) {
        multi_activity_actor::prune_dark_locations( you, wanted, get_type() );
    }
    if( order_complete ) {
        report_gear_up_finished( you );
    }
    return wanted;
}

// The base class ends the activity the moment a sweep comes up empty, and its
// per-turn source cache short-circuits multi_activity_locations(), which is
// where the equipment stage would otherwise hand over to supplies.  So the
// handover happens here, on the way out: without it a character whose last
// equipment find was on the last crate leaves with no ammunition, no bandages
// and no rations.
//
// The base class's ending rule is mirrored rather than called, because clearing
// the activity destroys this actor and everything after that has to be decided
// beforehand.
void multi_gear_up_activity_actor::do_turn( player_activity &act, Character &you )
{
    // A follower who fell asleep holding this order never acts on it again:
    // the sleeping AI does not run activities, so the job sits there and the
    // conversation option to re-issue it is hidden behind "already busy".
    // Waking here fixes the one already stuck as well as the next one.
    if( npc *guy = you.as_npc(); guy && guy->in_sleep_state() ) {
        talk_function::wake_up( *guy );
    }

    const activity_id prior_act = get_type();
    const bool activity_continues = simulate_turn( act, you, false );
    const bool travelling = you.has_destination();
    // Deliberately not the same question as whether there is an activity left to
    // clear: an NPC whose sweep runs out has already been reverted from under us
    // inside simulate_turn, which is exactly the case the handover exists for.
    const bool swept_out = !activity_continues && !travelling;
    const bool clearing = ( travelling || !activity_continues ) &&
                          !act.is_null() && prior_act == you.activity.id();

    bool resume = false;
    if( swept_out && you.gear_up_stage == static_cast<int>( gear_stage::equipment ) ) {
        you.gear_up_stage = static_cast<int>( gear_stage::supplies );
        resume = !tiles_wanted_for( you, gear_stage::supplies ).empty();
    }
    // Say so only when nothing anywhere is still wanted: ending because of a
    // blocked path is not the same as being finished.
    const bool finished = swept_out && !resume &&
                          tiles_wanted_for( you, static_cast<gear_stage>( you.gear_up_stage ) ).empty();

    if( clearing ) {
        // Destroys this actor.  Nothing below may touch `this` or `act`.
        you.activity = player_activity();
    }
    if( resume ) {
        you.assign_activity( multi_gear_up_activity_actor() );
    } else if( finished ) {
        report_gear_up_finished( you );
    }
}

activity_reason_info multi_gear_up_activity_actor::multi_activity_can_do( Character &you,
        const tripoint_bub_ms &src_loc )
{
    const gear_stage stage = static_cast<gear_stage>( you.gear_up_stage );
    if( !tile_has_anything_wanted( you, src_loc, stage ) ) {
        return activity_reason_info::fail( do_activity_reason::ALREADY_DONE );
    }
    return activity_reason_info::ok( do_activity_reason::NEEDS_GEAR_UP );
}

bool multi_gear_up_activity_actor::multi_activity_do( Character &you,
        const activity_reason_info &, const tripoint_abs_ms &, const tripoint_bub_ms &src_loc )
{
    // Going through a crate costs time whether or not anything comes of it.
    you.mod_moves( -search_cost_moves );

    const bool did_something =
        static_cast<gear_stage>( you.gear_up_stage ) == gear_stage::equipment
        ? do_equipment_stage( you, src_loc )
        : do_supply_stage( you, src_loc );

    // The per-turn scans name one specific item as the thing to go and get,
    // and working a tile invalidates that answer: the item is off the shelf,
    // or its type has just been turned down.  Either way every later question
    // this turn would match nothing and read as "nothing wanted anywhere",
    // which ends the sweep a couple of items in.  The scans still only run
    // once per pass over the locations, which is where the cost is.
    reset_gear_up_caches();

    if( npc *p = you.as_npc() ) {
        // Let the NPC's own AI re-examine what it is now carrying; it scores
        // weapons with the same function used here, so it will agree.
        p->has_new_items = true;
        p->invalidate_range_cache();
    }

    // false keeps the activity alive so a crate with several useful things is
    // not abandoned after one; true when nothing happened is the only thing
    // that lets the sweep run out and end.
    return !did_something;
}

bool gear_up_stores_available( Character &who )
{
    return !stores_within_reach( who ).empty();
}

void reset_gear_up_caches()
{
    gear_up_cache_generation++;

    // The framework caches its work locations across turns and prunes a tile
    // that answered "nothing here" permanently.  Which tile offers what depends
    // on the scans just invalidated above, so that answer has to be asked
    // again, or the sweep charges through a stale list and ends a couple of
    // items in.
    multi_zone_activity_actor::invalidate_source_cache();
}

void start_gear_up_from_stores( Character &who )
{
    // Reset the sweep here rather than in the actor's start(): multi-zone
    // actors are cloned through the backlog and restarted every turn, so state
    // reset there would drop back to the first stage forever.  A fresh order
    // reconsiders everything turned down last time -- the weather has moved on,
    // and so has what is in the crates.
    who.gear_up_rejected.clear();
    who.gear_up_stage = static_cast<int>( gear_stage::equipment );
    who.gear_up_done_reported = false;
    who.assign_activity( multi_gear_up_activity_actor() );
}

// Rummaging through crates with something hunting you is how people die.  The
// avatar is trusted to make that call themselves; an NPC given the order is
// not, because the player cannot see what the NPC can.
static bool hostiles_in_sight( npc &p )
{
    map &here = get_map();
    for( Creature &critter : g->all_creatures() ) {
        if( &critter == static_cast<Creature *>( &p ) ) {
            continue;
        }
        if( p.attitude_to( critter ) != Creature::Attitude::HOSTILE ) {
            continue;
        }
        if( rl_dist( p.pos_abs(), critter.pos_abs() ) > MAX_VIEW_DISTANCE / 3 ) {
            continue;
        }
        if( !p.sees( here, critter ) ) {
            continue;
        }
        add_msg( m_warning, _( "%1$s won't stop to sort gear with %2$s in sight." ), p.get_name(),
                 critter.disp_name() );
        return true;
    }
    return false;
}

void talk_function::gear_up_from_stores( npc &p )
{
    if( p.is_hallucination() || hostiles_in_sight( p ) ) {
        return;
    }

    if( !gear_up_stores_available( p ) ) {
        add_msg( m_info, _( "%s has no loot or camp storage zone in range to draw from." ),
                 p.get_name() );
        return;
    }

    // Preparing for a fight is reason enough to cut sleep short: an order
    // assigned to a sleeping follower otherwise sits there unstarted, since
    // the sleeping AI does not act on an activity at all.
    if( p.in_sleep_state() ) {
        wake_up( p );
    }

    start_gear_up_from_stores( p );
}
