//! todo: adding tests
use super::*;
use ::egui::{Event, Key, Modifiers};
use thiserror::Error;

#[derive(Debug, Default)]
pub struct HotkeyBuffer {
    intercept_for_text_edit: bool,
    number: Option<usize>,
    fragments: Vec<HotkeyFragment>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct HotkeyFragment {
    key: Key,
    modifiers: Modifiers,
    text: Option<String>,
}

impl IsHotkeyBuffer for HotkeyBuffer {}

impl HotkeyBuffer {
    pub fn intercept_for_text_edit(&self) -> bool {
        self.intercept_for_text_edit
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct HotkeyMap<T: Copy> {
    data: Vec<(HotkeyPattern, T)>,
}

impl<T: Copy> std::ops::Deref for HotkeyMap<T> {
    type Target = [(HotkeyPattern, T)];

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<'a, T: Copy> HotkeyMap<T> {
    pub fn new(iter: impl IntoIterator<Item = (&'a str, T)>) -> HotkeyPatternParseResult<Self> {
        Ok(Self {
            data: iter
                .into_iter()
                .map(|(s, t)| Ok((HotkeyPattern::from_str(s)?, t)))
                .collect::<HotkeyPatternParseResult<_>>()?,
        })
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct HotkeyPattern {
    fragments: Vec<HotkeyPatternFragment>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum HotkeyPatternFragment {
    Text(String),
    Modified {
        key: Key,
        modifiers_pattern: Modifiers,
    },
}

impl HotkeyPattern {
    pub fn from_str(s: &str) -> HotkeyPatternParseResult<Self> {
        let fragments = s.split(" ");
        Ok(Self {
            fragments: fragments
                .map(|s| HotkeyPatternFragment::from_str(s))
                .collect::<HotkeyPatternParseResult<_>>()?,
        })
    }
}

#[test]
fn hotkey_pattern_from_str_works() {
    fn t(input: &str, expect: &[HotkeyPatternFragment]) {
        let expect = HotkeyPattern {
            fragments: expect.to_vec(),
        };
        assert_eq!(HotkeyPattern::from_str(input).unwrap(), expect)
    }

    t("F", &[HotkeyPatternFragment::Text("F".to_string())]);
    t(
        "Ctrl+F",
        &[HotkeyPatternFragment::Modified {
            key: Key::F,
            modifiers_pattern: Modifiers::CTRL,
        }],
    );
}

impl HotkeyPatternFragment {
    fn from_str(s: &str) -> HotkeyPatternParseResult<Self> {
        let &[ref modifier_strs @ .., key_str] = &s.split("+").collect::<Vec<_>>() as &[&str]
        else {
            Err(HotkeyPatternParseError::ExpectedCharsBesidesPlus(
                s.to_string(),
            ))?
        };
        if modifier_strs.is_empty() {
            return Ok(HotkeyPatternFragment::Text(key_str.to_string()));
        }
        let mut modifiers_pattern = Modifiers::NONE;
        for &modifier_str in modifier_strs {
            match modifier_str {
                "C" | "Ctrl" | "CTRL" => modifiers_pattern.ctrl = true,
                "A" | "Alt" | "ALT" => modifiers_pattern.alt = true,
                "S" | "Shift" | "SHIFT" => modifiers_pattern.shift = true,
                _ => Err(HotkeyPatternParseError::NoModifierFromName(
                    modifier_str.to_string(),
                ))?,
            }
        }
        let key = Key::from_name(key_str)
            .ok_or(HotkeyPatternParseError::NoKeyFromName(key_str.to_string()))?;
        Ok(HotkeyPatternFragment::Modified {
            key,
            modifiers_pattern,
        })
    }
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum HotkeyPatternParseError {
    #[error("expected chars besides `+`")]
    ExpectedCharsBesidesPlus(String),
    #[error("no key from name")]
    NoKeyFromName(String),
    #[error("no modifier from name")]
    NoModifierFromName(String),
}

pub type HotkeyPatternParseResult<T> = Result<T, HotkeyPatternParseError>;

impl HotkeyBuffer {
    fn reset(&mut self) {
        self.number = None;
        self.fragments = Default::default()
    }

    pub fn set_intercept_for_text_edit(&mut self) {
        assert!(!self.intercept_for_text_edit);
        self.intercept_for_text_edit = true
    }
}

impl HotkeyBuffer {
    /// This method:
    /// 1. Converts input events into buffered key presses to be extracted later.
    /// 2. Resets the text edit interception flag.
    ///
    /// This should be invoked before rendering a frame
    pub fn start_frame(&mut self, ctx: &::egui::Context) {
        ctx.input(|i| self.start_frame_aux(&i.events));
    }

    fn start_frame_aux(&mut self, events: &[Event]) {
        self.absorb_events(events);
        // reset interception
        self.intercept_for_text_edit = false;
    }

    fn absorb_events(&mut self, events: &[Event]) {
        match HotkeyFragment::from_events(events, self.intercept_for_text_edit) {
            Ok(fragment) => self.absorb_fragment(fragment),
            Err(reset) => {
                if reset {
                    self.reset()
                }
            }
        }
    }

    fn absorb_fragment(&mut self, fragment: HotkeyFragment) {
        if self.fragments.is_empty() && fragment.modifiers.is_none() {
            if let Some(number) = number_str_from_key(fragment.key) {
                let text = fragment.text.as_ref().unwrap();
                if text.len() == 1 && text.chars().next().unwrap().is_digit(10) {
                    self.number = Some(match self.number {
                        Some(prev) => prev * 10 + number,
                        None => number,
                    });
                    return;
                }
            }
        }
        self.fragments.push(fragment)
    }

    pub fn extract<'a, T: Copy>(
        &mut self,
        hotkey_map: impl IntoIterator<Item = (&'a HotkeyPattern, T)>,
    ) -> Option<(Option<usize>, T)> {
        let extract = self.extract_aux(hotkey_map);
        if extract.is_some() {
            self.reset()
        }
        extract
    }

    fn extract_aux<'a, T: Copy>(
        &self,
        hotkey_map: impl IntoIterator<Item = (&'a HotkeyPattern, T)>,
    ) -> Option<(Option<usize>, T)> {
        hotkey_map
            .into_iter()
            .find(|(pattern, _)| pattern.recognize(&self.fragments))
            .map(|(_, t)| (self.number, t))
    }
}

fn number_str_from_key(key: Key) -> Option<usize> {
    match key {
        Key::Num0 => Some(0),
        Key::Num1 => Some(1),
        Key::Num2 => Some(2),
        Key::Num3 => Some(3),
        Key::Num4 => Some(4),
        Key::Num5 => Some(5),
        Key::Num6 => Some(6),
        Key::Num7 => Some(7),
        Key::Num8 => Some(8),
        Key::Num9 => Some(9),
        _ => None,
    }
}

impl HotkeyFragment {
    /// returns whether to reset or not if not a valid fragment
    fn from_events(events: &[Event], intercept_for_text_edit: bool) -> Result<Self, bool> {
        let mut slf: Option<Self> = None;
        let mut text: Option<String> = None;
        for event in events {
            match *event {
                Event::Text(ref text1) => {
                    if intercept_for_text_edit {
                        return Err(false);
                    }
                    assert!(text.is_none());
                    text = Some(text1.clone());
                }
                Event::Key {
                    key: Key::Escape, ..
                } => Err(true)?,
                Event::Key {
                    key,
                    pressed: true,
                    modifiers,
                    ..
                } => {
                    assert!(
                        slf.is_none(),
                        "slf ={:?}, event = {:?}, intercept_for_text_edit = {}",
                        slf,
                        event,
                        intercept_for_text_edit
                    );
                    slf = Some(HotkeyFragment {
                        key,
                        modifiers,
                        text: None,
                    })
                }
                _ => (),
            }
        }
        if let Some(text) = text {
            let mut slf = slf.unwrap();
            assert!(slf.text.is_none());
            slf.text = Some(text);
            return Ok(slf);
        }
        slf.ok_or(false)
    }
}

impl HotkeyPattern {
    fn recognize(&self, fragments: &[HotkeyFragment]) -> bool {
        if self.fragments.len() != fragments.len() {
            return false;
        }
        self.fragments
            .iter()
            .zip(fragments)
            .all(|(patt, key)| patt.recognize(key))
    }
}

impl HotkeyPatternFragment {
    fn recognize(&self, fragment: &HotkeyFragment) -> bool {
        match *self {
            HotkeyPatternFragment::Text(ref text) => match fragment.text {
                Some(ref text1) => text == text1,
                None => false,
            },
            HotkeyPatternFragment::Modified {
                key,
                modifiers_pattern,
            } => fragment.key == key && fragment.modifiers.matches_logically(modifiers_pattern),
        }
    }
}

#[test]
fn hotkey_buffer_works() {
    use expect_test::expect;

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    enum Action {
        Copy,
        Paste,
        Dance,
        Return,
    }
    use Action::*;

    fn t(
        events_sequence: &[&[Event]],
        expect: Option<(Option<usize>, Action)>,
        intercept_for_text_edit: bool,
        hotkey_map: &HotkeyMap<Action>,
    ) {
        let mut buffer = HotkeyBuffer::default();
        for (i, events) in events_sequence.iter().enumerate() {
            buffer.intercept_for_text_edit = intercept_for_text_edit;
            buffer.start_frame_aux(events);
            let extract = buffer.extract(hotkey_map);
            assert_eq!(
                extract,
                (i + 1 == events_sequence.len()).then_some(expect).flatten()
            )
        }
    }

    let hotkey_map = HotkeyMap::new([("Alt+F R", Return)]).unwrap();
    expect![[r#"
        HotkeyMap {
            data: [
                (
                    HotkeyPattern {
                        fragments: [
                            Modified {
                                key: F,
                                modifiers_pattern: Modifiers {
                                    alt: true,
                                },
                            },
                            Text(
                                "R",
                            ),
                        ],
                    },
                    Return,
                ),
            ],
        }
    "#]]
    .assert_debug_eq(&hotkey_map);
    t(&[], None, false, &hotkey_map);
    t(
        &[&[
            Event::Text("F".to_string()),
            Event::Key {
                key: Key::F,
                physical_key: None,
                pressed: true,
                repeat: false,
                modifiers: Modifiers::ALT,
            },
        ]],
        None,
        false,
        &hotkey_map,
    );
    t(
        &[
            &[
                Event::Text("F".to_string()),
                Event::Key {
                    key: Key::F,
                    physical_key: None,
                    pressed: true,
                    repeat: false,
                    modifiers: Modifiers::ALT,
                },
            ],
            &[
                Event::Text("R".to_string()),
                Event::Key {
                    key: Key::R,
                    physical_key: None,
                    pressed: true,
                    repeat: false,
                    modifiers: Modifiers::NONE,
                },
            ],
        ],
        Some((None, Return)),
        false,
        &hotkey_map,
    );
    t(
        &[
            &[
                Event::Text("1".to_string()),
                Event::Key {
                    key: Key::Num1,
                    physical_key: None,
                    pressed: true,
                    repeat: false,
                    modifiers: Modifiers::NONE,
                },
            ],
            &[
                Event::Text("F".to_string()),
                Event::Key {
                    key: Key::F,
                    physical_key: None,
                    pressed: true,
                    repeat: false,
                    modifiers: Modifiers::ALT,
                },
            ],
            &[
                Event::Text("R".to_string()),
                Event::Key {
                    key: Key::R,
                    physical_key: None,
                    pressed: true,
                    repeat: false,
                    modifiers: Modifiers::NONE,
                },
            ],
        ],
        Some((Some(1), Return)),
        false,
        &hotkey_map,
    );
    t(
        &[
            &[
                Event::Text("1".to_string()),
                Event::Key {
                    key: Key::Num1,
                    physical_key: None,
                    pressed: true,
                    repeat: false,
                    modifiers: Modifiers::NONE,
                },
            ],
            &[
                Event::Text("F".to_string()),
                Event::Key {
                    key: Key::F,
                    physical_key: None,
                    pressed: true,
                    repeat: false,
                    modifiers: Modifiers::ALT,
                },
            ],
            &[Event::Key {
                key: Key::Escape,
                physical_key: None,
                pressed: true,
                repeat: false,
                modifiers: Modifiers::ALT,
            }],
            &[
                Event::Text("R".to_string()),
                Event::Key {
                    key: Key::R,
                    physical_key: None,
                    pressed: true,
                    repeat: false,
                    modifiers: Modifiers::NONE,
                },
            ],
        ],
        None,
        false,
        &hotkey_map,
    );
    t(
        &[
            &[
                Event::Text("1".to_string()),
                Event::Key {
                    key: Key::Num1,
                    physical_key: None,
                    pressed: true,
                    repeat: false,
                    modifiers: Modifiers::NONE,
                },
            ],
            &[
                Event::Text("F".to_string()),
                Event::Key {
                    key: Key::F,
                    physical_key: None,
                    pressed: true,
                    repeat: false,
                    modifiers: Modifiers::ALT,
                },
            ],
            &[Event::Key {
                key: Key::Escape,
                physical_key: None,
                pressed: true,
                repeat: false,
                modifiers: Modifiers::ALT,
            }],
            &[
                Event::Text("F".to_string()),
                Event::Key {
                    key: Key::F,
                    physical_key: None,
                    pressed: true,
                    repeat: false,
                    modifiers: Modifiers::ALT,
                },
            ],
            &[
                Event::Text("R".to_string()),
                Event::Key {
                    key: Key::R,
                    physical_key: None,
                    pressed: true,
                    repeat: false,
                    modifiers: Modifiers::NONE,
                },
            ],
        ],
        Some((None, Return)),
        false,
        &hotkey_map,
    );
}

impl<'a, T: Copy> IntoIterator for &'a HotkeyMap<T> {
    type Item = (&'a HotkeyPattern, T);
    type IntoIter = std::iter::Map<
        std::slice::Iter<'a, (HotkeyPattern, T)>,
        fn(&'a (HotkeyPattern, T)) -> (&'a HotkeyPattern, T),
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.data.iter().map(|(pattern, value)| (pattern, *value))
    }
}
