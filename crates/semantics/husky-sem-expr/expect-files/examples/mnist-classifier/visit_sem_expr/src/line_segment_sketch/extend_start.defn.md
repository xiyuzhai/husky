```rust
Some(
    [
        "end",
        "let mut start = end",
        "ct",
        "end",
        "start",
        "1",
        "start - 1",
        "ct.displacement(end, start - 1)",
        "let mut dp0 = ct.displacement(end, start - 1)",
        "end",
        "ct",
        "ct.points",
        "ct.points.ilen()",
        "end - ct.points.ilen()",
        "let min_start = end - ct.points.ilen()",
        "start",
        "min_start",
        "start >= min_start",
        "dp0",
        "dp0.norm()",
        "r",
        "dp0.norm() < r",
        "start >= min_start and dp0.norm() < r",
        "start >= min_start and dp0.norm() < r",
        "start",
        "start--",
        "start--",
        "dp0",
        "ct",
        "end",
        "start",
        "1",
        "start - 1",
        "ct.displacement(end, start - 1)",
        "dp0 = ct.displacement(end, start - 1)",
        "dp0 = ct.displacement(end, start - 1)",
        "while start >= min_start and dp0.norm() < r:\n        start--\n        dp0 = ct.displacement(end, start - 1)",
        "dp0",
        "dp0.norm()",
        "r",
        "dp0.norm() < r",
        "dp0.norm() < r",
        "start",
        "start0",
        "start.min(start0)",
        "return start.min(start0)",
        "if dp0.norm() < r:\n        return start.min(start0)",
        "go_right",
        "dp0",
        "r",
        "go_right(dp0, r)",
        "let mut right_bound = go_right(dp0, r)",
        "go_left",
        "dp0",
        "r",
        "go_left(dp0, r)",
        "let mut left_bound = go_left(dp0, r)",
        "0.0",
        "let mut r_max = 0.0",
        "start",
        "min_start",
        "start >= min_start",
        "start >= min_start",
        "ct",
        "end",
        "start",
        "1",
        "start - 1",
        "ct.displacement(end, start - 1)",
        "let dp = ct.displacement(end, start - 1)",
        "dp",
        "dp.norm()",
        "let dp_norm = dp.norm()",
        "dp_norm",
        "r_max",
        "r",
        "r_max - r",
        "dp_norm < r_max - r",
        "dp_norm < r_max - r",
        "break",
        "dp_norm",
        "r_max",
        "dp_norm > r_max",
        "dp_norm > r_max",
        "r_max",
        "dp_norm",
        "r_max = dp_norm",
        "r_max = dp_norm",
        "if dp_norm < r_max - r:\n            break\n        elif dp_norm > r_max:\n            r_max = dp_norm",
        "dp_norm",
        "r",
        "dp_norm > r",
        "dp_norm > r",
        "go_right",
        "dp",
        "r",
        "go_right(dp, r)",
        "let dp_right = go_right(dp, r)",
        "go_left",
        "dp",
        "r",
        "go_left(dp, r)",
        "let dp_left = go_left(dp, r)",
        "right_bound",
        "dp_right",
        "right_bound.rotation_direction_to(dp_right)",
        "0",
        "right_bound.rotation_direction_to(dp_right) > 0",
        "right_bound.rotation_direction_to(dp_right) > 0",
        "right_bound",
        "dp_right",
        "right_bound = dp_right",
        "right_bound = dp_right",
        "if right_bound.rotation_direction_to(dp_right) > 0:\n                right_bound = dp_right",
        "dp_left",
        "left_bound",
        "dp_left.rotation_direction_to(left_bound)",
        "0",
        "dp_left.rotation_direction_to(left_bound) > 0",
        "dp_left.rotation_direction_to(left_bound) > 0",
        "left_bound",
        "dp_left",
        "left_bound = dp_left",
        "left_bound = dp_left",
        "if dp_left.rotation_direction_to(left_bound) > 0:\n                left_bound = dp_left",
        "if dp_norm > r:\n            let dp_right = go_right(dp, r)\n            let dp_left = go_left(dp, r)\n            if right_bound.rotation_direction_to(dp_right) > 0:\n                right_bound = dp_right\n            if dp_left.rotation_direction_to(left_bound) > 0:\n                left_bound = dp_left",
        "right_bound",
        "left_bound",
        "right_bound.rotation_direction_to(left_bound)",
        "0",
        "right_bound.rotation_direction_to(left_bound) >= 0",
        "right_bound.rotation_direction_to(left_bound) >= 0",
        "start",
        "start0",
        "start <= start0",
        "right_bound",
        "dp",
        "right_bound.rotation_direction_to(dp)",
        "0",
        "right_bound.rotation_direction_to(dp) >= 0",
        "dp",
        "left_bound",
        "dp.rotation_direction_to(left_bound)",
        "0",
        "dp.rotation_direction_to(left_bound) >= 0",
        "right_bound.rotation_direction_to(dp) >= 0 \n                        and dp.rotation_direction_to(left_bound) >= 0",
        "(\n                        right_bound.rotation_direction_to(dp) >= 0 \n                        and dp.rotation_direction_to(left_bound) >= 0\n                    )",
        "!(\n                        right_bound.rotation_direction_to(dp) >= 0 \n                        and dp.rotation_direction_to(left_bound) >= 0\n                    )",
        "start <= start0 \n                    and !(\n                        right_bound.rotation_direction_to(dp) >= 0 \n                        and dp.rotation_direction_to(left_bound) >= 0\n                    )",
        "start <= start0 \n                    and !(\n                        right_bound.rotation_direction_to(dp) >= 0 \n                        and dp.rotation_direction_to(left_bound) >= 0\n                    )",
        "break",
        "if start <= start0 \n                    and !(\n                        right_bound.rotation_direction_to(dp) >= 0 \n                        and dp.rotation_direction_to(left_bound) >= 0\n                    ):\n                break",
        "start",
        "start--",
        "start--",
        "break",
        "if right_bound.rotation_direction_to(left_bound) >= 0:\n            if start <= start0 \n                    and !(\n                        right_bound.rotation_direction_to(dp) >= 0 \n                        and dp.rotation_direction_to(left_bound) >= 0\n                    ):\n                break\n            start--\n        else:\n            break",
        "while start >= min_start:\n        let dp = ct.displacement(end, start - 1)\n        let dp_norm = dp.norm()\n        if dp_norm < r_max - r:\n            break\n        elif dp_norm > r_max:\n            r_max = dp_norm\n        if dp_norm > r:\n            let dp_right = go_right(dp, r)\n            let dp_left = go_left(dp, r)\n            if right_bound.rotation_direction_to(dp_right) > 0:\n                right_bound = dp_right\n            if dp_left.rotation_direction_to(left_bound) > 0:\n                left_bound = dp_left\n        if right_bound.rotation_direction_to(left_bound) >= 0:\n            if start <= start0 \n                    and !(\n                        right_bound.rotation_direction_to(dp) >= 0 \n                        and dp.rotation_direction_to(left_bound) >= 0\n                    ):\n                break\n            start--\n        else:\n            break",
        "start",
        "start0",
        "start <= start0",
        "start <= start0",
        "start",
        "return start",
        "start0",
        "return start0",
        "if start <= start0:\n        return start\n    else:\n        return start0",
        "let mut start = end\n    let mut dp0 = ct.displacement(end, start - 1)\n    let min_start = end - ct.points.ilen()\n    while start >= min_start and dp0.norm() < r:\n        start--\n        dp0 = ct.displacement(end, start - 1)\n    if dp0.norm() < r:\n        return start.min(start0)\n    let mut right_bound = go_right(dp0, r)\n    let mut left_bound = go_left(dp0, r)\n    let mut r_max = 0.0\n    while start >= min_start:\n        let dp = ct.displacement(end, start - 1)\n        let dp_norm = dp.norm()\n        if dp_norm < r_max - r:\n            break\n        elif dp_norm > r_max:\n            r_max = dp_norm\n        if dp_norm > r:\n            let dp_right = go_right(dp, r)\n            let dp_left = go_left(dp, r)\n            if right_bound.rotation_direction_to(dp_right) > 0:\n                right_bound = dp_right\n            if dp_left.rotation_direction_to(left_bound) > 0:\n                left_bound = dp_left\n        if right_bound.rotation_direction_to(left_bound) >= 0:\n            if start <= start0 \n                    and !(\n                        right_bound.rotation_direction_to(dp) >= 0 \n                        and dp.rotation_direction_to(left_bound) >= 0\n                    ):\n                break\n            start--\n        else:\n            break\n    //assert start <= start0\n    if start <= start0:\n        return start\n    else:\n        return start0",
    ],
)
```