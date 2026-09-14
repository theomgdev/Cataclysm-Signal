#include <vector>

#include "bodypart.h"
#include "calendar.h"
#include "cata_catch.h"
#include "character.h"
#include "game.h"
#include "game_constants.h"
#include "player_helpers.h"
#include "skill.h"
#include "units.h"

static const skill_id skill_bashing( "bashing" );

TEST_CASE( "skill_rust_occurs", "[character][skill]" )
{
    Character &guy = get_player_character();
    clear_avatar();

    // Set every skill to two, so they can rust
    for( const Skill &skill : Skill::skills ) {
        INFO( skill.ident().str() );
        guy.set_skill_level( skill.ident(), 2 );
        REQUIRE( guy.get_skill_level( skill.ident() ) == 2.f );
        REQUIRE( guy.get_knowledge_level( skill.ident() ) == 2 );
        REQUIRE_FALSE( guy.get_skill_level_object( skill.ident() ).isRusty() );
    }

    // Wait three days
    for( int i = 0; i < to_seconds<int>( 3_days ); ++i ) {
        calendar::turn += 1_seconds;
        guy.update_body();
        if( calendar::once_every( 4_hours ) ) {
            // Don't starve
            guy.set_stored_kcal( guy.get_healthy_kcal() );
            // Clear thirst and sleepiness
            guy.environmental_revert_effect();
            // And sleep deprivation
            guy.set_sleep_deprivation( 0 );
        }
    }

    // Ensure they have rusted
    for( const Skill &skill : Skill::skills ) {
        INFO( skill.ident().str() );
        // Rust is about 1% per day with a one day grace period
        CHECK( guy.get_skill_level( skill.ident() ) < 2.f );
        CHECK( guy.get_skill_level( skill.ident() ) > 1.5f );
        CHECK( guy.get_knowledge_level( skill.ident() ) == 2 );
        CHECK( guy.get_skill_level_object( skill.ident() ).isRusty() );
    }
}

TEST_CASE( "stats_are_trained_by_skills", "[character][skill][stats]" )
{
    Character &guy = get_player_character();
    clear_avatar();
    guy.set_str_base( 8 );
    const int base_str = guy.get_str_base();
    guy.reset();

    REQUIRE( guy.get_stat_training( character_stat::STRENGTH ) == 0 );
    REQUIRE( guy.get_str() == base_str );

    SECTION( "practice raises the stat and never lowers it" ) {
        int previous = guy.get_stat_training( character_stat::STRENGTH );
        for( int level = 1; level <= MAX_SKILL; ++level ) {
            guy.set_skill_level( skill_bashing, level );
            guy.reset();
            const int trained = guy.get_stat_training( character_stat::STRENGTH );
            INFO( "bashing level " << level );
            CHECK( trained >= previous );
            previous = trained;
        }
        CHECK( previous > 0 );
    }

    SECTION( "a lifetime of practice stops short of doubling the stat" ) {
        for( const Skill &skill : Skill::skills ) {
            guy.set_skill_level( skill.ident(), MAX_SKILL );
        }
        guy.reset();
        CHECK( guy.get_stat_training( character_stat::STRENGTH ) < base_str );
        CHECK( guy.get_str() < 2 * base_str );
        CHECK( guy.get_str() > base_str );
    }

    SECTION( "the trained points reach carry weight and max hp" ) {
        const units::mass base_capacity = guy.weight_capacity();
        const int base_hp = guy.get_part_hp_max( body_part_torso );
        for( const Skill &skill : Skill::skills ) {
            guy.set_skill_level( skill.ident(), MAX_SKILL );
        }
        guy.reset();
        CHECK( guy.weight_capacity() > base_capacity );
        CHECK( guy.get_part_hp_max( body_part_torso ) > base_hp );
    }

    SECTION( "rust gives the points back" ) {
        guy.set_skill_level( skill_bashing, MAX_SKILL );
        guy.reset();
        const int trained = guy.get_stat_training( character_stat::STRENGTH );
        REQUIRE( trained > 0 );
        guy.set_skill_level( skill_bashing, 1 );
        guy.reset();
        CHECK( guy.get_stat_training( character_stat::STRENGTH ) < trained );
    }
}
