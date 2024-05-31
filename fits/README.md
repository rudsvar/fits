# fits

A simple interpreted language that's all about structural typing.

```ts
// Has a field `name`.
type Animal {
    name: String
}

// Has all fields from `Animal` and `age`.
type Dog < Animal {
    age: Int

    function bark(self) {
        print("Boof!");
    }
}

// Accepts anything with the fields and methods of `Dog`.
function acceptDog(dog: Dog) { ... }

type Bark {
    function bark(self): String;
}

// Accepts anything with the methods defined in `Bark`.
function acceptBark(bark: Bark) { ... }

// Anonymous implementation of `Bark`.
acceptBark({ bark: \self -> print("Bork!") })
```
