```rust
Some(
    [
        "u",
        "u.x",
        "u",
        "u.x",
        "u.x*u.x",
        "u",
        "u.y",
        "u",
        "u.y",
        "u.y*u.y",
        "u.x*u.x+u.y*u.y",
        "(u.x*u.x+u.y*u.y)",
        "(u.x*u.x+u.y*u.y).sqrt()",
        "let L = (u.x*u.x+u.y*u.y).sqrt()",
        "L",
        "r",
        "L > r",
        "L > r",
        "assert L > r",
        "r",
        "L",
        "r*L",
        "L",
        "L",
        "L*L",
        "r",
        "r",
        "r*r",
        "L*L-r*r",
        "(L*L-r*r)",
        "(L*L-r*r).sqrt()",
        "r*L/(L*L-r*r).sqrt()",
        "let dr = r*L/(L*L-r*r).sqrt()",
        "dr",
        "u",
        "u.y",
        "dr*u.y",
        "L",
        "dr*u.y/L",
        "let dx = dr*u.y/L",
        "dr",
        "-dr",
        "u",
        "u.x",
        "-dr*u.x",
        "L",
        "-dr*u.x/L",
        "let dy = -dr*u.x/L",
        "Vector2d",
        "u",
        "u.x",
        "dx",
        "u.x+dx",
        "u",
        "u.y",
        "dy",
        "u.y+dy",
        "Vector2d(u.x+dx, u.y+dy)",
        "Vector2d(u.x+dx, u.y+dy)",
        "let L = (u.x*u.x+u.y*u.y).sqrt()\n    assert L > r\n    let dr = r*L/(L*L-r*r).sqrt()\n    let dx = dr*u.y/L\n    let dy = -dr*u.x/L\n    Vector2d(u.x+dx, u.y+dy)",
    ],
)
```