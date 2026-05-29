/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//! This module contains properties that API-level entities should satisfy.

use crate::roundtrip_entities::pretty_assert_entities_deep_eq;
use cedar_policy::{Entities, Entity, PolicySet, Template};

/// An [`Entity`] should roundrtrip through serialization with json and then deserialization.
/// The [`Entity`] gets converted to a singleton [`Entities`].
pub fn entity_to_json_roundtrips(original: Entity) {
    // Wrap in Entities for JSON serialization
    let entities = Entities::from_entities([original.clone()], None)
        .expect("Failed to create Entities from single entity");
    entities_to_json_roundtrips(entities);
}

/// An [`Entities`] should roundtrip through serialization with json and then deserialization.
pub fn entities_to_json_roundtrips(original: Entities) {
    // Serialize to JSON
    let json = original.to_json_value().unwrap_or_else(|e| {
        panic!(
            "Entity accepted from proto could not be serialized to JSON.\n\
             Proto input: {:?}\nError: {e}",
            e
        )
    });

    // Re-parse from JSON
    let roundtripped = Entities::from_json_value(json.clone(), None).unwrap_or_else(|e| {
        panic!(
            "JSON from proto-accepted entity failed to re-parse.\n\
             Proto input: {:?}\nJSON: {json}\nParse error: {e}",
            e
        )
    });

    pretty_assert_entities_deep_eq(&original, &roundtripped);
}

/// A [`Template`] should print to Cedar and parse again. This function panic for inputs where
/// it does not.
pub fn template_to_cedar_parses(original: Template) {
    // Print to Cedar text
    let cedar_text = original.to_cedar();

    // Re-parse (templates parse as part of a policy set)
    let _: cedar_policy::PolicySet = cedar_text.parse().unwrap_or_else(|e| {
        panic!(
            "This cedar_policy::Template cannot be printed and parsed:\n{:?}\nParse error: {e}",
            original
        )
    });
}

/// A [`PolicySet`] should print to Cedar and parse again. This function panic for inputs where
/// it does not.
pub fn policyset_to_cedar_parses(original: PolicySet) {
    // Print the whole policy set to Cedar text
    let cedar_text = original.to_cedar().unwrap_or_else(|| {
        panic!(
            "Policy set could not be printed to Cedar.\nPolicySet: {:?}",
            original
        )
    });

    // Re-parse the Cedar text; this should succeed
    let _: PolicySet = cedar_text.parse().unwrap_or_else(|e| {
        panic!(
            "Cedar text from PolicySet failed to re-parse.\n\
             Original: {:?}\nCedar text: {cedar_text}\nParse error: {e}",
            original
        )
    });
}
