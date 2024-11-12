# LaTeX (the Husky version)

In the normal language, text -> token -> ast -> syn expr -> sema expr.

However, here text <--> token <--> ast -> syn expr -> sema expr.

Further text <--> token <--> ast is totally handled automatically.

Basically, the user modify directly the asts.

LaTex asts is centered around displayability, what looks the same is processed the same way.

We differs from the standard implementation of LaTex in that

- greek letters like `α`, `β`, ... and special symbols like `∀`, `∃` are allowed for better readability;
- `{...}` in math mode can be interpreted directly as set notation if the content inside doesn't begin with `_` or `^`;
- all `/` is interpreted as fraction, and thus no fraction command is needed for faster typing;
- ...

Our LaTex is designed to be as a limited yet more structured subset of LaTex as possible for easier data acquirement. It should yield meaningful error messages for AI agents to fix. We'll gradually add more features to it as we see fit.

Modes:

- root.
- rose. English. Rose as a word can mean a stylized representation of the flower in heraldry or decoration, typically with five petals (especially as a national emblem of England).