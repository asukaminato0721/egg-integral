# egg-integral

use [egg](https://egraphs-good.github.io/) with [rubi](https://rulebasedintegration.org/) to do integral.

## TODO

- [ ] select test-case
- [x] a tool to auto convert mathematica to egg rule
- [ ] benchmark

## Compare to current available tools

- open source
- rule based, easier to understand than Risch algorithm && add new rules.
- step by step
- speed

---

## Development

```sh
git clone https://github.com/RuleBasedIntegration/Rubi
git clone <this repo>
cd <this repo>
python gen.py
cargo build # currently will fail
```

---

## TODO

1. egg can't do complex condtion check. (Or I haven't figure out how to do it.)
   ```rs
    | expected an `Fn(&mut egg::EGraph<_, _>, egg::Id, &egg::Subst)` closure, found `bool`
    | required by a bound introduced by this call
   ```

   ```rs
   rw!("id", "left" => "right", if cond1 if cond2)
   ```

   can't be written into

   ```rs
   rw!("id", "left" => "right", if cond1 && cond2)
   ```

   so how to express `||` is a problem. Maybe split into 2 rules?

2. support more ignored functions.
3. how to support `D[f, n]` ?
