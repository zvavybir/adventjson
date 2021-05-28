A simple JSON library

This is a simple JSON library I wrote for one of the [advent of
code](https://adventofcode.com/) challenges, but became a full,
standard complaint JSON parser.  To use it just call the
`JsonObject::read` function with what you want to have parsed:

```rust
use adventjson::JsonObject;

let s = "{\"hello\": \"World\", \"answer\": 42}";
let json_object = JsonObject::read(s)?;

assert_eq!(format!("{}", json_object), s);
```

# License
This library is distributed under the GPL license.
