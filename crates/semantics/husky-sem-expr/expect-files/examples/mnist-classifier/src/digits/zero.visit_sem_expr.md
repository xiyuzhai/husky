## `open_one_match` decl

```rust
Some(
    [
        "FermiMatchResult",
    ],
)
```

## `open_one_match` defn

```rust
Some(
    [
        "fermi_match",
        "major_concave_components",
        "almost_closed",
        "[almost_closed]",
        "fermi_match(major_concave_components, [almost_closed])",
        "fermi_match(major_concave_components, [almost_closed])",
        "fermi_match(major_concave_components, [almost_closed])",
    ],
)
```

## `almost_closed` decl

```rust
Some(
    [
        "ConcaveComponent",
        "~ConcaveComponent",
        "f32",
        "?f32",
    ],
)
```

## `almost_closed` defn

```rust
Some(
    [
        "cc",
        "cc.angle_change",
        "0.0",
        "cc.angle_change + 0.0",
        "140.0",
        "-140.0",
        "cc.angle_change + 0.0 < -140.0",
        "cc.angle_change + 0.0 < -140.0",
        "require cc.angle_change + 0.0 < -140.0",
        "cc",
        "cc.angle_change",
        "-cc.angle_change",
        "0.0",
        "-cc.angle_change + 0.0",
        "-cc.angle_change + 0.0",
        "require cc.angle_change + 0.0 < -140.0\n    -cc.angle_change + 0.0",
    ],
)
```

## `is_zero` decl

```rust
Some(
    [
        "OneVsAll",
        "MnistLabel",
        "OneVsAll MnistLabel",
        "MnistLabel::Zero",
        "OneVsAll MnistLabel MnistLabel::Zero",
    ],
)
```

## `is_zero` defn

```rust
Some(
    [
        "major_connected_component",
        "major_connected_component.raw_contours",
        "major_connected_component.raw_contours.ilen()",
        "1",
        "major_connected_component.raw_contours.ilen() == 1",
        "major_connected_component.raw_contours.ilen() == 1",
        "open_one_match",
        "open_one_match.norm",
        "let n = open_one_match.norm",
        "n",
        "1.5",
        "n < 1.5",
        "n < 1.5",
        "require n < 1.5",
        "open_one_match",
        "open_one_match.matches",
        "0",
        "open_one_match.matches[0]",
        "open_one_match.matches[0] be Some(_)",
        "require open_one_match.matches[0] be Some(_)",
        "connected_components",
        "connected_components.ilen()",
        "1",
        "connected_components.ilen() == 1",
        "connected_components.ilen() == 1",
        "require connected_components.ilen() == 1",
        "open_one_match",
        "open_one_match.matches",
        "0",
        "open_one_match.matches[0]",
        "open_one_match.matches[0]!",
        "open_one_match.matches[0]!.displacement()",
        "open_one_match.matches[0]!.displacement().norm()",
        "let c = open_one_match.matches[0]!.displacement().norm()",
        "c",
        "5.5",
        "c < 5.5",
        "c < 5.5",
        "require c < 5.5",
        "OneVsAll::Yes",
        "return OneVsAll::Yes",
        "if major_connected_component.raw_contours.ilen() == 1:\n        let n = open_one_match.norm\n        require n < 1.5\n        require open_one_match.matches[0] be Some(_)\n        require connected_components.ilen() == 1\n        let c = open_one_match.matches[0]!.displacement().norm()\n        require c < 5.5\n        return OneVsAll::Yes",
        "fermi_match",
        "major_concave_components",
        "[]",
        "fermi_match(major_concave_components, [])",
        "let simp_zero_match = fermi_match(major_concave_components, [])",
        "narrow_down",
        "simp_zero_match",
        "simp_zero_match.norm",
        "simp_zero_match",
        "simp_zero_match.rel_norm",
        "simp_zero_match",
        "simp_zero_match.angle_change_norm",
        "5",
        "narrow_down(\n        simp_zero_match.norm,\n        simp_zero_match.rel_norm,\n        simp_zero_match.angle_change_norm,\n        skip = 5\n    )",
        "narrow_down(\n        simp_zero_match.norm,\n        simp_zero_match.rel_norm,\n        simp_zero_match.angle_change_norm,\n        skip = 5\n    )?",
        "narrow_down(\n        simp_zero_match.norm,\n        simp_zero_match.rel_norm,\n        simp_zero_match.angle_change_norm,\n        skip = 5\n    )?",
        "simp_zero_match",
        "simp_zero_match.norm",
        "3.0",
        "simp_zero_match.norm < 3.0",
        "simp_zero_match.norm < 3.0",
        "require simp_zero_match.norm < 3.0",
        "major_connected_component",
        "major_connected_component.eff_holes",
        "major_connected_component.eff_holes.matches",
        "1",
        "major_connected_component.eff_holes.matches[1]",
        "major_connected_component.eff_holes.matches[1] be None",
        "require major_connected_component.eff_holes.matches[1] be None",
        "major_connected_component",
        "major_connected_component.eff_holes",
        "major_connected_component.eff_holes.matches",
        "0",
        "major_connected_component.eff_holes.matches[0]",
        "major_connected_component.eff_holes.matches[0] be Some(_)",
        "require major_connected_component.eff_holes.matches[0] be Some(_)",
        "major_connected_component",
        "major_connected_component.eff_holes",
        "major_connected_component.eff_holes.matches",
        "0",
        "major_connected_component.eff_holes.matches[0]",
        "let major_hole = major_connected_component.eff_holes.matches[0]",
        "major_hole",
        "major_hole!",
        "major_hole!.bounding_box",
        "major_hole!.bounding_box.ymax()",
        "major_hole",
        "major_hole!",
        "major_hole!.bounding_box",
        "major_hole!.bounding_box.ymin()",
        "major_hole!.bounding_box.ymax() - major_hole!.bounding_box.ymin()",
        "let a = major_hole!.bounding_box.ymax() - major_hole!.bounding_box.ymin()",
        "major_line_segment_sketch",
        "major_line_segment_sketch.bounding_box",
        "major_line_segment_sketch.bounding_box.ymax()",
        "major_line_segment_sketch",
        "major_line_segment_sketch.bounding_box",
        "major_line_segment_sketch.bounding_box.ymin()",
        "major_line_segment_sketch.bounding_box.ymax() - major_line_segment_sketch.bounding_box.ymin()",
        "let b = major_line_segment_sketch.bounding_box.ymax() - major_line_segment_sketch.bounding_box.ymin()",
        "a",
        "b",
        "a/b",
        "let ratio = a/b",
        "ratio",
        "0.4",
        "ratio > 0.4",
        "ratio > 0.4",
        "require ratio > 0.4",
        "simp_zero_match",
        "simp_zero_match.norm",
        "let a = simp_zero_match.norm",
        "OneVsAll::Yes",
        "OneVsAll::Yes",
        "if major_connected_component.raw_contours.ilen() == 1:\n        let n = open_one_match.norm\n        require n < 1.5\n        require open_one_match.matches[0] be Some(_)\n        require connected_components.ilen() == 1\n        let c = open_one_match.matches[0]!.displacement().norm()\n        require c < 5.5\n        return OneVsAll::Yes\n    let simp_zero_match = fermi_match(major_concave_components, [])\n    narrow_down(\n        simp_zero_match.norm,\n        simp_zero_match.rel_norm,\n        simp_zero_match.angle_change_norm,\n        skip = 5\n    )?\n    require simp_zero_match.norm < 3.0\n    require major_connected_component.eff_holes.matches[1] be None\n    // require major_concave_components.ilen() <= 1 failed\n    require major_connected_component.eff_holes.matches[0] be Some(_)\n    let major_hole = major_connected_component.eff_holes.matches[0]\n    let a = major_hole!.bounding_box.ymax() - major_hole!.bounding_box.ymin()\n    let b = major_line_segment_sketch.bounding_box.ymax() - major_line_segment_sketch.bounding_box.ymin()\n    // high_point, low_point\n    let ratio = a/b\n    require ratio > 0.4\n    let a = simp_zero_match.norm\n    OneVsAll::Yes",
    ],
)
```
