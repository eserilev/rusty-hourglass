# Hourglass

A world that remembers. 

## What it is for

A world holds entities i.e. people, places, and things. Facts change that world
over time. The changes are permanent: a king dies and stays dead, a
house burns and stays burned

Two products consume it. Sandcastle generates games for children, and
its server is Rust. A later game server holds one shared world. The
crate serves both, so it depends on neither.

Hourglass is the world and its rules. It is NOT the storyteller. A
director called SandMan sits outside, asks a model what happens next,
and proposes it. Hourglass says yes or no, and remembers.

The goal is to build a ruleset for this ever evolving world. This allows LLM's
to propose changes and code decides wether the change is allowed or not.

## The four questions

Every decision belongs to one of these.

1. What is a world made of?
2. How does it change?
3. Who decides the change?
4. What stops a bad change?

## Decided

### From question 1: what a world is made of

1. **Entities are a flat list.** Nothing contains anything. There is no
   nesting in the data.
2. **Each entity says where it is.** One place at a time. Ada is in the
   mill, the mill is in Ashford. Walk up to get the city.
3. **Location is not belonging.** Ada travels and her location changes.
   Ada stays a citizen of Ashford. Those are two different things.
4. **An entity has a type**, from a closed list: Person, Place, Thing,
   Faction. A closed list lets the rules refuse "the sword died".
   Faction is in because a war, a crown, and a family outlive their
   members.
5. **Existence is a stretch of time**, not an alive flag. A history
   engine must answer "was Ada alive when the mill burned". A flag
   answers only "is Ada alive now".
6. **That stretch is called a `TimeSpan`.**
7. **A fact is a struct of its own.** A fact is a thing that is true of
   an entity. The mill is burned. Ada is king. Decision 15 says for how
   long it stays in the state.
8. **A fact carries a number when it needs one.** A city treasury is
   4000, then 900. The number moves at story speed, so the history
   holds it. A player's coin purse moves at player speed, so it does
   not.
9. **A fact does not end because somebody dies.** A grudge outlives the
   person. A crown does not. The rule differs per fact, so the engine
   cannot pick one answer for all of them.

### From question 2: how a world changes

Decisions 21 to 24 sit here too. They are about facts, so they belong
to question 1, but each one was settled by an argument about the log.

10. **The `EventLog` is the truth.** Every change is an event. The
    `EventLog` is append-only and ordered. Nothing is edited, and
    nothing is removed.
11. **The state is derived.** `apply(state, event)` takes one event
    and returns the next state. `replay(log)` runs `apply` over the
    whole `EventLog` and rebuilds the state from nothing.
12. **`apply` is the only writer.** Nothing sets a fact directly.
    Break this and the `EventLog` and the state drift apart, and then
    neither one is worth trusting.

```
EventLog                               the truth. append-only, ordered.
   │
   │  apply, one event at a time
   ▼
state    BTreeMap<EntityId, Entity>    derived. entities, each with facts.
   │
   │  render
   ▼
prompt   text for the director
```

13. **Both halves feed the prompt.** A director reads neither the
    `EventLog` nor the state. It reads a prompt built from both. "How things are
    now" comes from the state — who is king, how bad the famine is.
    "What just happened" comes from the tail of the `EventLog`. A
    director needs the first before it proposes anything.

That is why neither half is optional. An `EventLog` with no state means
a full `replay` on every prompt, and that gets slower as the world gets
older. A state with no `EventLog` loses why anything happened.

14. **The name is `Fact`.** `Claim` is reserved. When the world gains
    "who knows this", a fact becomes something believed, and `Claim` is
    the right word for that layer.
15. **The state is the present. The `EventLog` is the past.** A fact
    that ends leaves the state. It is still in the log, so nothing is
    lost, and memory stays the size of the world today instead of the
    size of its whole history. So a `Fact` has no end.

    One exception: an entity stays in the state after it dies, because
    the history names it and other facts point at it. `existence` keeps
    its full `TimeSpan`. An entity is permanent and a fact is not.
16. **A `Fact` points at the event that opened it**, and stores no time
    of its own.

    ```rust
    struct Fact { name: ???, value: Option<i64>, opened: EventId }
    ```

    The tick comes from `log[opened].tick`, so nothing is duplicated.
    The same field is the cause: "why is the mill burned" is one hop to
    the event that burned it.
17. **The same events always give the same state.** `replay` on one
    `EventLog` builds one state, on any machine, in any run. This is
    not a wish. It is a property `apply` must hold, and five things
    break it:

    - **Unordered collections.** A `HashMap` iterates in a different
      order each run. Use `BTreeMap` and `BTreeSet`, always.
    - **Floats.** An `f64` gives different answers on different
      hardware. Values are `i64`. There is no float anywhere.
    - **The clock.** `apply` never reads the system time. Time comes
      from the tick on the event.
    - **Randomness.** `apply` never draws from an unseeded source. A
      seed is stored, in the event or in the world.
    - **Anything outside.** `apply` reads its two arguments and nothing
      else. No files, no network, no globals.

    **This says nothing about the director.** A language model given
    one world proposes something different every time, and that is
    fine. The log records what was ACCEPTED. Producing a log is not
    reproducible; replaying one is. Chains draw the same line: making a
    block is not deterministic, executing it is.
18. **The state holds a `Fact`, not a pointer to an event.** The state
    is a copy, and a copy is the point: it describes the PRESENT on its
    own. Who exists, where they are, what is true. Snapshots, a state
    sent to a client, and a row in a database all need that without the
    whole history, and a state of `Vec<EventId>` gives none of it.

    It does NOT promise to answer *when*. "How long has the famine run"
    is `log[opened].tick`, and that needs the log. Adding `since: Tick`
    to a fact would buy duration without the log, and nothing asks for
    that yet.
19. **An event and a fact are separate types.** They look alike and
    they differ by one field each, in opposite directions:

    ```rust
    FactStart { entity, name, value, to }         // knows WHO holds it
    Fact      {         name, value, to, opened } // knows WHICH event made it
    ```

    The event carries `entity` because the log is flat. The fact does
    not, because it already sits on its entity. The fact carries
    `opened`; the event cannot, because that points at itself.

    Sharing the middle three fields in a nested struct costs
    `fact.body.name` at every call site, forever, to save three fields.
    Not worth it.
20. **Two event kinds so far: `FactStart` and `FactEnd`.** `FactStart`
    makes a fact true. `FactEnd` takes it out of the state. Both stay
    in the `EventLog` forever, so "the mill burned in year 51 and was
    rebuilt in year 58" still answers.

    The word "Fact" in the name says what the event ACTS ON. Not every
    event touches a fact — founding an entity and moving one do not.

21. **A fact name is a `String`, checked against a declared list.**
    Not an interned number. The protection from "treasury" becoming
    "treasure" comes from CHECKING against a declared list, and never
    from interning. Interning is a separate job, and mixing the two
    produced `FactId`, `def.def`, and a design nobody could read.

    Measured, interning saves about 120 KB on a thousand entities and
    a few thousand short string compares a tick. It costs a serialized
    state of `{"name": 2}` instead of `{"name": "burned"}`, which you
    read constantly while debugging a model, and a vocabulary that must
    never be reordered or every old log silently changes meaning. If
    profiling ever disagrees, interning is a change inside the crate
    that no caller sees.
22. **`FactVocabulary` maps a name to its rules.**

    ```rust
    struct FactVocabulary(BTreeMap<String, FactRules>);
    ```

    `validate` refuses a name the vocabulary does not hold. That list
    is also what a director prompt carries: a closed set in, a closed
    set out.
23. **`FactRules` is an enum, not a struct of flags.** A flat struct
    lets a person declare nonsense — a rule about a target on a name
    that has no target. The field that changes what the other fields
    MEAN becomes the tag:

    ```rust
    enum FactRules {
        Solo   { numeric: bool },   // burned, treasury
        Linked { numeric: bool },   // king_of, hates
    }
    ```

    `numeric` is the only rule decided today. Cardinality is open, and
    it lands inside these variants when it is decided.

    This is worth doing HERE and not on `Fact`, because a person writes
    `FactRules` by hand, once per name. A `Fact` is built by `apply`
    from an event that `validate` already checked.
24. **A link is one flat field on `Fact`.** No separate type, and no
    enum.

    ```rust
    struct Fact {
        name: String,
        value: Option<i64>,
        linked_to: Option<EntityId>,
        opened: EventId,
    }
    ```

    An enum makes two bad states unrepresentable — a solo fact with a
    target, and a linked fact without one. It costs four variants,
    because `value` has the same problem, and eight if a third rule
    ever arrives. `validate` closes both holes at the one place that
    already reads the rules.

    The name pairs with `FactRules::Linked`, and the reverse query
    names itself: `facts_linked_to(bren)`.

25. **Cardinality is a `Count` on each side of the link.**

    ```rust
    enum Count { One, Many, AtMost(u16) }

    enum FactRules {
        Solo   { numeric: bool },
        Linked {
            numeric: bool,
            holders: Count,   // how many entities hold this about one target
            targets: Count,   // how many targets one entity holds it about
        },
    }
    ```

    Real declarations read as a sentence:

    ```rust
    king_of      Linked { holders: One,         targets: Many }  // one king each city
    citizen_of   Linked { holders: Many,        targets: One  }  // one citizenship each
    married_to   Linked { holders: One,         targets: One  }
    hates        Linked { holders: Many,        targets: Many }
    council_of   Linked { holders: AtMost(12),  targets: Many }  // twelve on Ashford's council
    ```

    Two sides, because the two limits are different and each is wanted
    without the other. `king_of` blocks a second king of Ashford, and
    allows Ada to rule two cities. `citizen_of` does the reverse.

    Two fields and not one enum of the four cases. The axes are
    independent, so an enum has to spell out the cross product, and its
    both-at-once arm repeats the checks from the other two. An enum is
    for when one choice changes what the others mean — which is why
    `Solo` against `Linked` IS an enum.

    `AtMost` works on either side, and it is a real case, not a
    hypothetical: twelve councillors of Ashford, three advisors to a
    king, fifty in a garrison. Another city gets its own twelve.

    `One` is `AtMost(1)` with a better name at the declaration site.
    One method collapses the redundancy, so the validator has a single
    path:

    ```rust
    impl Count {
        fn limit(self) -> Option<u16> {
            match self { One => Some(1), AtMost(n) => Some(n), Many => None }
        }
    }
    ```

    This is also why `Count` beats a `unique: bool`. A bool says one or
    unlimited and can never say twelve, so the day a council arrives
    you rename the field and touch every declaration.

    One thing here is not a rule. A mill cannot be burned twice at
    once, because `FactStart` closes any open fact of the same name on
    that entity. One-per-entity is built in, not declared.

### From question 3: who decides the change

26. **The director lives outside this crate.** It is called SandMan.
    Hourglass holds the world, the rules, and the log. SandMan reads
    the world, asks a model what happens next, and hands back proposed
    events.

    ```
    SandMan  ── proposes an event ──▶  Hourglass
             ◀── accepted, or refused with a reason ──
    ```

    Hourglass never calls a model and never sees a prompt. No I/O, no
    async, nothing that fails at random. That is what keeps `replay`
    deterministic and the tests fast, and it is the whole reason the
    boundary sits here.

    So there is no `Director` trait in the crate.
27. **Hourglass picks what matters. The consumer writes the words.**

    ```rust
    world.view(for_entity, budget) -> View   // structured. no text.
    ```

    A world of five hundred entities does not fit in a prompt. Choosing
    the twenty that matter needs the graph, the vocabulary, and the
    rules, and both consumers need the same answer. So that job is
    here.

    The words are not. Sandcastle talks to a nine-year-old, maybe in
    Hebrew. A game server talks in a fantasy register. Same data, and
    completely different text.

    The deciding argument is a rule Sandcastle already lives by: a
    prompt is a file, read on every call, never compiled in. A crate
    that emits prompt text turns every wording change into a crate
    release.
28. **Salience needs no new types.** "What has this player touched" is
    facts:

    ```
    player  visited      ──▶ the mill
    player  met          ──▶ Ada
    player  bought_from  ──▶ the merchant
    ```

    Linked facts, `holders: Many`, `targets: Many`. Ranking is a query
    over facts, not a new structure. `view` uses it to choose the
    twenty, and a director uses it to choose which house burns. A
    random house means nothing. The house the player slept in is a
    story.
29. **There is no player type.** A player is a `Person`. The consumer
    holds the mapping from an account to an `EntityId`, and Hourglass
    never learns what an account is. "Who is looking" is an argument to
    `view`, not a field on an entity.

## In chain terms

The shape is a chain, so the words carry over:

| Hourglass | Ethereum |
|---|---|
| `Event` | a transaction |
| `EventLog` | the chain |
| state — entities and facts | world state |
| `validate` | validity rules |
| `apply` | the state transition function |
| `replay` | sync from genesis |
| a snapshot at a cut | checkpoint sync |
| hash-link | parent hash |

Three places the comparison breaks, and each one saves work:

**There is no adversary.** No consensus, no forks to resolve, no fee
market, no denial of service to defend. The only writer is your own
director. Build none of that.

**A rejection is the normal path, not an attack.** On a chain an invalid
transaction is a bug or an attack. Here a language model guesses, gets
refused, and tries again — that is the design working. So a rejection
must be feedback a director reads and acts on. A boolean is not enough.

**Rollback is a real requirement, and it is cheap here.** Sandcastle
already gives a child undo and checkpoints. Undo is a rollback: cut the
`EventLog` at a point and `replay` it. That costs nothing because
`apply` builds state from nothing. State that changed in place would
need a reverse operation for every kind of event.

## The types

Ten types are agreed. Each one below says what it is and why it
exists.

**`EntityId`** — Uniquely identifies an entity

**`EventId`** — the position of one event in the `EventLog`.

**`Tick`** — one step of world time. A tick is not a frame. It is as
long as the game says: an hour, a day, a season.

**`TimeSpan`** — a stretch of time. It has a start, and it has an end
or it is still going. Only `Entity::existence` uses it, because an
entity stays in the state after it dies. A `Fact` leaves the state, so
it needs none.

**`EntityType`** — what an entity is, from a closed list. The list is
closed because a rule can only refuse what the types name. With a
closed list the engine refuses "the sword died" and "the faction is in
the mill". With free text it cannot.

**`Entity`** — one person, place, thing, or faction. It carries a name
that a person reads, a type, and two things that make it real: where it
sits, and how long it has been here. `location` holds one parent, so a
thing is in exactly one place. `existence` is a `TimeSpan`, so the world
knows Ada was alive in year 12 and gone by year 50.

**`Fact`** — one thing that is true of an entity RIGHT NOW. The mill is
burned. The treasury holds 4000. Ada is king of Ashford. A fact holds no
time of its own. It points at the event that opened it, and that event
carries the tick and the reason. When a fact ends it leaves the state,
and the `EventLog` keeps it.

**`FactVocabulary`** — every fact name one world knows, and the rules
for each. `validate` refuses a name that is not in it. The same list
goes into a director prompt, so the model chooses from a closed set.

**`FactRules`** — the rules for one name. Is it a number or a flag.
Does it name a second entity. How many links each side allows. An enum,
so a rule that needs a target cannot be declared on a name that has
none.

**`Count`** — `One`, `Many`, or `AtMost(n)`. It caps each side of a
link. `holders: One` means Ashford has one king. `targets: One` means
Ada has one spouse. `holders: AtMost(12)` means twelve sit on Ashford's
council, and the next city gets its own twelve.

### Where each type lives

| Type | Lives in |
|---|---|
| `Event`, `FactStart`, `FactEnd` | the `EventLog` |
| `Entity`, `Fact` | the state |
| `FactVocabulary`, `FactRules` | the world, beside both |
| `EntityId`, `EventId`, `Tick`, `TimeSpan`, `EntityType` | both |

Nothing in the state is an event. A director hands back a PROPOSED
event, so one exists in flight for a moment. Only an accepted one
reaches the log.

## The names

These names are agreed. The shapes below hold ONLY the agreed parts.
Every gap is marked, and a gap is not a hint.

```rust
/// A handle on one entity. Never reused: the history names the dead.
struct EntityId(u32);

/// The position of one event in the EventLog.
struct EventId(u64);

/// One step of world time. As long as the game says.
struct Tick(u64);

/// A stretch of time that started and maybe ended.
struct TimeSpan { from: Tick, until: Option<Tick> }

/// What an entity is. A closed list.
enum EntityType { Person, Place, Thing, Faction }

/// One person, place, thing, or faction.
struct Entity {
    id: EntityId,
    entity_type: EntityType,
    name: String,
    /// Where it sits. One parent, never two. Not belonging.
    location: Option<EntityId>,
    /// Started, and maybe ended. One span, ever.
    existence: TimeSpan,
    facts: Vec<Fact>,
}

/// A thing that is true of an entity right now.
struct Fact {
    /// Checked against the vocabulary. Never a free string.
    name: String,
    /// A number, when the fact needs one. A treasury does.
    value: Option<i64>,
    /// The second entity, when the name takes one. None for a
    /// one-sided fact like "burned".
    linked_to: Option<EntityId>,
    /// The event that made this true. It carries the tick and the
    /// reason, so a fact stores no time of its own.
    opened: EventId,
}

/// Every fact name this world knows, and the rules for each.
struct FactVocabulary(BTreeMap<String, FactRules>);

/// The rules for one name. An enum, so nonsense cannot be declared.
enum FactRules {
    Solo   { numeric: bool },
    Linked { numeric: bool, holders: Count, targets: Count },
}

/// How many of something one rule allows.
/// `One` is `AtMost(1)`, spelled for the reader.
enum Count { One, Many, AtMost(u16) }
```

`existence` keeps its own name. It is a `TimeSpan`, and the word says
what the span is for. It is the only `TimeSpan` left.

## Open

Not decided. Do not build these.

- **One-of-a-kind solo facts.** Only one city is the capital. Decision
  25 caps each side of a LINK, and says nothing about a solo fact that
  only one entity in the world can hold. No consumer has asked.
- **The rest of the event set.** Decision 20 names `FactStart` and
  `FactEnd`. Founding an entity, ending one, and moving one all need
  events too, and none of them is named yet.
- **Is a value change one event or two?** The treasury goes from 4000
  to 900. Two events — `FactEnd` then `FactStart` — and the log says
  exactly what it did. One event — `FactStart` alone, and `apply`
  ends any open fact of that name — and the log carries a hidden
  side effect. I lean two.
- **Walking a fact backwards.** Decision 15 sends an ended fact out of
  the state, so "who was king in year 30" scans the `EventLog`. The fix
  is a back-pointer on the EVENT, not on the fact:

  ```rust
  struct Event { /* ... */ prev_for_subject: Option<EventId> }
  ```

  Each event points at the last event that touched the same entity and
  the same name. History becomes a linked list, and the query walks a
  few hops instead of scanning. One `EventId` per event, and it lives
  in the log, so it survives after the fact leaves the state. Do not
  build it until something is slow.
- **Pruning and snapshots.** A world that runs for years grows an
  `EventLog` that never stops. Dropping the old part needs a rolled-up
  state at the cut. Not decided, and not needed for a first world.

  Pruning breaks decision 16. A `Fact` holds `opened: EventId`, and a
  pruned event leaves that pointing at nothing. Any pruning design must
  answer this — most likely by rewriting a surviving fact to point at
  the snapshot.

  It also loses duration for good. Once the opening event is gone,
  nothing knows when the famine started. A snapshot has to carry the
  ticks that the dropped events held, or facts have to gain a
  `since: Tick`.
- **The shape of a rejection.** "In chain terms" says a rejection is
  feedback, not a boolean. What that feedback holds is open.
- **Does `replay` re-validate?** Two answers, both defensible. Trusting
  the log is fast, because every event in it passed `validate` once.
  Re-running `validate` catches a bug in `apply` and a log somebody
  edited by hand, which is what a full node does.

  Re-validating raises a second question. Rules change. A rule added in
  year two rejects an event that was legal in year one, and then an old
  log stops replaying. Chains answer that with fork rules. Not decided.
- **A state root.** A hash over the whole state, not over the events.
  A chain hash proves two parties saw the same events. A state root
  proves they COMPUTED the same state, and that is the stronger claim:
  a bug in `apply` leaves the chain hash equal and the state root
  different. For a server and a client holding one world, the state
  root is the number worth comparing. Not decided.
- **Hash-linking.** Each event carries the hash of the one before it.
  Then one number names the exact state of a world, and a server and a
  client compare that number to find a disagreement at once. Cheap and
  liked, not decided. It demands one thing: serialization must be
  deterministic, so no floats and no unordered maps, ever.
- **What `View` holds.** Decision 27 says the crate chooses and the
  consumer words it. The shape of what comes back is open, and it is
  the risky boundary: too little and a consumer reaches into the state
  anyway, too much and it is the state with extra steps.
- **How salience is scored.** Decision 28 says the inputs are facts.
  How they rank is open.
- **The rules.** Question 4. Nothing is decided beyond what each
  decision above already forces.

## Rules for this crate

1. Hourglass depends on nothing in `server/`.
2. Nothing goes in until a consumer asks for it.
3. Nothing goes in this file until Eitan agrees to it.
