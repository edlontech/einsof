mod extraction;

use serde::{Deserialize, Serialize};

pub use extraction::{ExtractionConfig, ExtractionMode, ExtractionProviderConfig};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum OperationalMode {
    #[default]
    Development,
    Production {
        strict: bool,
    },
}

impl Serialize for OperationalMode {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeMap;
        match self {
            OperationalMode::Development => serializer.serialize_str("development"),
            OperationalMode::Production { strict } => {
                let mut map = serializer.serialize_map(Some(2))?;
                map.serialize_entry("mode", "production")?;
                map.serialize_entry("strict", strict)?;
                map.end()
            }
        }
    }
}

impl<'de> Deserialize<'de> for OperationalMode {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::{MapAccess, Visitor};

        struct OperationalModeVisitor;

        impl<'de> Visitor<'de> for OperationalModeVisitor {
            type Value = OperationalMode;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter
                    .write_str("\"development\" or {\"mode\": \"production\", \"strict\": bool}")
            }

            fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                match value {
                    "development" => Ok(OperationalMode::Development),
                    _ => Err(E::custom(format!("unknown mode: {}", value))),
                }
            }

            fn visit_map<M>(self, mut map: M) -> Result<Self::Value, M::Error>
            where
                M: MapAccess<'de>,
            {
                let mut mode: Option<String> = None;
                let mut strict: Option<bool> = None;

                while let Some(key) = map.next_key::<String>()? {
                    match key.as_str() {
                        "mode" => mode = Some(map.next_value()?),
                        "strict" => strict = Some(map.next_value()?),
                        _ => {
                            let _: serde::de::IgnoredAny = map.next_value()?;
                        }
                    }
                }

                match mode.as_deref() {
                    Some("production") => Ok(OperationalMode::Production {
                        strict: strict.unwrap_or(false),
                    }),
                    Some("development") => Ok(OperationalMode::Development),
                    Some(other) => {
                        Err(serde::de::Error::custom(format!("unknown mode: {}", other)))
                    }
                    None => Err(serde::de::Error::missing_field("mode")),
                }
            }
        }

        deserializer.deserialize_any(OperationalModeVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn operational_mode_defaults_to_development() {
        let mode = OperationalMode::default();
        assert!(matches!(mode, OperationalMode::Development));
    }

    #[test]
    fn operational_mode_serializes_correctly() {
        let dev = OperationalMode::Development;
        let json = serde_json::to_string(&dev).unwrap();
        assert_eq!(json, "\"development\"");

        let prod = OperationalMode::Production { strict: true };
        let json = serde_json::to_string(&prod).unwrap();
        assert!(json.contains("\"production\""));
        assert!(json.contains("\"strict\":true"));
    }

    #[test]
    fn operational_mode_deserializes_from_string() {
        let mode: OperationalMode = serde_json::from_str("\"development\"").unwrap();
        assert!(matches!(mode, OperationalMode::Development));
    }

    #[test]
    fn operational_mode_deserializes_from_map() {
        let json = r#"{"mode": "production", "strict": true}"#;
        let mode: OperationalMode = serde_json::from_str(json).unwrap();
        assert!(matches!(mode, OperationalMode::Production { strict: true }));
    }

    #[test]
    fn operational_mode_strict_defaults_to_false() {
        let json = r#"{"mode": "production"}"#;
        let mode: OperationalMode = serde_json::from_str(json).unwrap();
        assert!(matches!(
            mode,
            OperationalMode::Production { strict: false }
        ));
    }
}
