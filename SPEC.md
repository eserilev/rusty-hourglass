# Hourglass

A world that remembers. 

Status: THE CRATE IS BUILT. The crate holds all five
build steps: the types, `apply` and `replay`, `located_in` with
the containment queries, `validate` with every rejection, and
`brief`. It holds two parts more, because the first consumer
asked for them: the memory of a run (`memory.rs`) and the schema
that grows (`migrate.rs`). A `verify` referee folds the history a
second time and checks twelve invariants. Sixty-six tests pass,
and ten Kani harnesses prove the join laws per value, the direction
law, and the band laws. `merge` applies the join name by name.
Aeneas translates the scalar core and the record merge to Lean.
Fifty-five Lean theorems hold for every input with no bound
(`lean/README.md`): the ten Kani laws, panic freedom of the join,
and the record laws. A merge answers the same in either order, and
it ignores the grouping. A merge with itself or with an empty
record changes nothing. A merge of two records that fit gives a
record that fits. The
seeded sweep against a naive oracle stays as a second check. Six
more theorems hold the history discipline for every `apply` and
every `validate`: a replay gives the live world, a rewind is exact,
and a refused proposal changes nothing. Six more hold the rules
inside `apply` for every world that commits build: one fact per
slot, one fact per single-target name, and an entity never
vanishes. Six more hold the band law of the gate: in every world
that proposals build, every fact carries a declared name, and every
number sits inside the band of its name. Six more hold the
direction law: in every world that proposals build, a fact of an
`Up` name never falls and never ends. Six more hold the count
laws: in every world that proposals build, no target has more
holders than its name allows, and no entity holds more targets.
Seven more hold the ring law: in every world that proposals build,
no place sits inside itself. No consumer calls the crate yet.

The build went past the decisions below in eleven places. The
section "Built past the decisions" names each one. Read that
section before the code, and reject what you do not want.

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
   mill, the mill is in Ashford. Walk up to get the city. Decision 32
   says this is a fact, not a field.
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

10. **The `EventHistory` is the truth.** Every change is an event. The
    `EventHistory` is append-only and ordered. Nothing is edited, and
    nothing is removed.
11. **The state is derived.** `apply(state, event)` takes one event
    and returns the next state. `replay(log)` runs `apply` over the
    whole `EventHistory` and rebuilds the state from nothing.
12. **`apply` is the only writer.** Nothing sets a fact directly.
    Break this and the `EventHistory` and the state drift apart, and then
    neither one is worth trusting.

```
EventHistory                           the truth. append-only, ordered.
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
    `EventHistory` nor the state. It reads a prompt built from both. "How things are
    now" comes from the state — who is king, how bad the famine is.
    "What just happened" comes from the tail of the `EventHistory`. A
    director needs the first before it proposes anything.

That is why neither half is optional. An `EventHistory` with no state means
a full `replay` on every prompt, and that gets slower as the world gets
older. A state with no `EventHistory` loses why anything happened.

14. **The name is `Fact`.** `Claim` is reserved. When the world gains
    "who knows this", a fact becomes something believed, and `Claim` is
    the right word for that layer.
15. **The state is the present. The `EventHistory` is the past.** A fact
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
    `EventHistory` builds one state, on any machine, in any run. This is
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
20. **`FactStart` and `FactEnd`.** `FactStart` makes a fact true.
    `FactEnd` takes it out of the state. Both stay in the
    `EventHistory` forever, so "the mill burned in year 51 and was
    rebuilt in year 58" still answers. Decision 31 holds the full
    set.

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
            // decision 33 adds `allowed` here
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

30. **`EventHistory` is a type, not a bare `Vec`.** Decision 10 says
    append-only. A `Vec` lets anyone call `.remove(3)`, and a rule that
    lives only in a comment is a rule that breaks.

    ```rust
    struct EventHistory(Vec<Event>);

    impl EventHistory {
        fn push(&mut self, e: Event) -> EventId;   // the only way in
        fn get(&self, id: EventId) -> Option<&Event>;
        fn tail(&self, n: usize) -> &[Event];
        fn next_id(&self) -> EventId;
        fn len(&self) -> usize;
    }
    ```

    No `remove`, no `clear`, no `IndexMut`. The guarantee lives on the
    type, so it holds wherever the value goes.

    **One exception, and it is deliberate.** "In chain terms" says
    rollback is a real requirement — a child's undo cuts the history
    and replays it. So there is exactly one method that shortens the
    history:

    ```rust
    fn truncate(&mut self, after: EventId);
    ```

    One way to shorten it, named so it cannot happen by accident.

31. **Five event kinds. That is the whole set.**

    ```rust
    enum EventKind {
        EntityCreated   { id, entity_type, name },
        EntityDestroyed { id },
        FactStart       { entity, name, value, linked_to },
        FactUpdate      { entity, name, linked_to, from: i64, to: i64 },
        FactEnd         { entity, name, linked_to },
    }
    ```

    Derived from what the state holds. An entity has a type, a name, a
    location, an existence, and facts. Each of those changes, or it
    does not.

    `EntityCreated` is the one people ask about. Why not a fact? A fact
    lives INSIDE an entity, so there has to be a row before anything is
    true of it. And the event is not there to record the creation date
    — `existence.from` already holds that. It is there because
    `replay` rebuilds the state from the history, and a change that is
    not in the history does not survive a replay.

    Moving is not here. Decision 32 makes location a fact, so a move
    is a `FactStart`. Placing a new entity is a `FactStart` too, so
    `EntityCreated` carries no location. One event, one change.

    `FactUpdate` is decision 33½. A house that burns and is rebuilt
    reads like this, and rebuilding is a `FactEnd`, not a new entity:

    ```
    [10]  EntityCreated { 7, Place, "the Cooper house" }
    [10]  FactStart     { 7, located_in → Ashford }
    [51]  FactStart     { 7, burned }
    [58]  FactEnd       { 7, burned }
    ```

    Same id throughout, so everyone who lived there still points at it.
    `EntityDestroyed` is for a house that is gone for good, never for
    one that needs repair.

    Two things are NOT events, on purpose:

    - **A type never changes.** A Person does not become a Place.
    - **A name never changes.** A city renamed after a conquest is
      real, and nothing has asked for it.

32. **Location is a fact, and `located_in` is reserved.**

    ```rust
    located_in   Linked { numeric: false, holders: Many, targets: One }
    ```

    `targets: One` gives one place at a time. A move is a `FactStart`,
    which closes the old one. `Entity.location` is gone, and so is
    `EntityMoved`.

    The reason is decision 5, applied again. A field is overwritten, so
    "where was Ada when the mill burned" has no answer. A fact leaves
    the old one in the history, so it does.

    **The crate declares the name itself**, in every vocabulary, so a
    consumer never types it and never misspells it:

    ```rust
    const LOCATED_IN: &str = "located_in";
    ```

    Because the crate knows that one name, it can offer the queries a
    consumer would otherwise write twice:

    ```rust
    world.contents(mill)     // who is in there
    world.ancestry(ada)      // the mill, then Ashford
    ```

    And it can refuse a cycle. Ashford inside the mill inside Ashford
    hangs any walk up the chain, so that check stays in `validate`.

33. **A linked fact declares which entity types it allows**, as a map
    from holder to targets.

    ```rust
    Linked {
        numeric: bool,
        holders: Count,
        targets: Count,
        allowed: BTreeMap<EntityType, Vec<EntityType>>,   // empty = any
    }
    ```

    ```rust
    located_in   Person => [Place],
                 Thing  => [Person, Place],
                 Place  => [Place]

    king_of      Person => [Place]

    hates        {}
    ```

    It reads as the rule itself. A Person goes in a Place. A Thing goes
    in a Person or a Place.

    **Two lists do not work.** `holder_types: [Person, Thing, Place]`
    and `target_types: [Place, Person]` allow every combination of the
    two — six, when four are wanted. `Person => Person` slips in, and
    "Ada is inside Bren" passes. A map cannot leak a corner, because
    each holder names its own targets.

    **One mechanism, nothing hardcoded.** An earlier draft kept a
    special `EntityType::can_contain` table for `located_in` alone.
    That gave the crate's own fact an exact rule that no consumer
    could use, for one job. This map serves every fact, and
    `located_in` is only different in that the crate declares it.

    `BTreeMap` and not `HashMap`, for decision 17.

33½. **`FactUpdate` changes a number.** The treasury falls from 4000
    to 900.

    ```
    [3]   FactStart  { Ashford, treasury, 4000 }
    [40]  FactUpdate { Ashford, treasury, 4000 -> 900 }
    ```

    Three reasons over a second `FactStart`:

    - **No hidden side effect.** A second `FactStart` silently ends the
      first, so the history shows a start and hides an end. This says
      it is a change.
    - **`from` is a stale check.** A director reads a briefing, thinks,
      and proposes. If the treasury moved meanwhile, `from: 4000` no
      longer matches and `validate` refuses it as a `Contradiction`.
      That is a compare-and-swap, and it matters when the proposer
      works from a snapshot.
    - **Narration gets the delta free.** "The treasury fell by 3100."

    `from` is derivable from the state, so it is duplication. The stale
    check earns it.

    **Numbers only.** A flag has no value to change, so `validate`
    refuses `FactUpdate` on one. And it cannot change a NAME: `burned`
    becoming `grand` is one fact ending and another starting, because
    `FactUpdate` holds one `name`.

    Inside, it is still an end and a start, because decision 15 says a
    new value is a new fact. One line in the history for two things in
    the state.

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
    world.brief(for_entity, budget) -> Briefing   // structured. no text.
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
    over facts, not a new structure. `brief` uses it to choose the
    twenty, and a director uses it to choose which house burns. A
    random house means nothing. The house the player slept in is a
    story.
29. **There is no player type.** A player is a `Person`. The consumer
    holds the mapping from an account to an `EntityId`, and Hourglass
    never learns what an account is. "Who is looking" is an argument to
    `brief`, not a field on an entity.

### From question 4: what stops a bad change

34. **The vocabulary goes into the prompt.** It already holds every
    rule that does not depend on the world: the names, which take a
    number, which take a target, how many, and which entity types.
    That is machine-readable, so the crate renders it:

    ```
    burned      a flag, on anything
    treasury    a number, on anything
    king_of     a flag, Person to Place, one king per place
    hates       a number, Person to Person, any many
    ```

    Same move as Sandcastle's sprite names: a closed list in, a closed
    list out. This removes every SHAPE mistake before the model runs —
    an invented name, a missing number, a wrong type.
35. **Rejections carry the rest, because the rest is about the world.**
    No text up front prevents these:

    ```
    Ashford already has a king
    Ada is dead
    that would put Ashford inside itself
    ```

    They are not facts about the fact. They are facts about the state
    right now. So the two layers are not alternatives. The vocabulary
    catches shape, and a rejection catches situation.
36. **A refusal returns every reason at once.** Not the first one. One
    retry then fixes everything, instead of one round trip per mistake.
37. **A tick proposes several events, and each stands alone.** The good
    ones land, and only the bad ones come back. A bad proposal costs
    one event, never the whole tick.

    All-or-nothing is what makes an LLM loop expensive. Partial
    acceptance is the fix, and it is free — `validate` already runs per
    event.

38. **A rejection is `Malformed` or `Contradiction`.** Both break a
    rule. They differ in WHICH rule, and the difference tells SandMan
    what to do.

    ```rust
    enum Rejection {
        /// Wrong on its own. Checking it needs only the vocabulary.
        Malformed(Malformed),
        /// Fine on its own. It contradicts the world as it is now.
        Contradiction(Contradiction),
    }

    enum Malformed {
        UnknownFact    { name: String },
        NeedsNumber    { name: String },
        TakesNoNumber  { name: String },
        NeedsTarget    { name: String },
        TakesNoTarget  { name: String },
        TypeNotAllowed { name: String, holder: EntityType, target: EntityType },
    }

    enum Contradiction {
        UnknownEntity  { id: EntityId },
        Gone           { id: EntityId },
        SelfReference  { id: EntityId },
        Cycle          { entity: EntityId, through: EntityId },
        TooManyHolders { name: String, target: EntityId, held_by: Vec<EntityId>, limit: u16 },
        TooManyTargets { name: String, holder: EntityId, pointing_at: Vec<EntityId>, limit: u16 },
    }
    ```

    A `Malformed` means the PROMPT failed. Decision 34 put the whole
    vocabulary in front of the model, and the model ignored it. A
    `Contradiction` means the model was reasonable and the world moved.
    Fix the prompt, or retry with fresh context. Two different
    responses, so they are two different types.

39. **A rejection names what is in the way.** That is the "how to fix",
    and it is data, not prose:

    ```
    TooManyHolders { name: "king_of", target: Ashford, held_by: [Ada], limit: 1 }
    ```

    End Ada's `king_of`, and the retry lands. The crate says what
    blocks it. It does NOT say what to do about it — crowning Bren
    somewhere else is an equally good answer, and the crate cannot know
    which one the story wants. That is the boundary from decision 26.

    This forces one thing on `validate`: it gathers the blockers before
    it refuses. It cannot return early on the first failure.

40. **No prose in a `Rejection`.** Words live outside, per decision 27.
    A `Display` impl gives a default line, and SandMan words it its own
    way.

41. **`Briefing` is what the crate hands SandMan.** Two cuts, not one.

    ```rust
    world.brief(for_entity, budget) -> Briefing

    struct Briefing {
        entities: Vec<&Entity>,   // the ones that matter, as they are NOW
        recent:   &[Event],       // the last few things that happened, anywhere
    }
    ```

    ```
    Briefing for Ada

    entities   Ada          king of Ashford
               Ashford      treasury 900
               The Mill     burned
               Bren         hates Ada

    recent     [51] the mill burned
               [52] treasury fell to 900
               [53] Elin died
    ```

    Entities are cut by what matters, and carry the present, not their
    history. Events are cut by recency, across the whole world, not per
    entity. It is not a history query. It is one snapshot plus one
    tail, which is decision 13 made concrete.

    In a small world — a child's game with thirty entities — the cut
    does nothing and the briefing is the whole state. The cut exists
    for the world with five hundred.

    The word is `Briefing` and not `Snapshot`, because the spec already
    uses "snapshot" for a rolled-up state at a cut in the history.

## In chain terms

The shape is a chain, so the words carry over:

| Hourglass | Ethereum |
|---|---|
| `Event` | a transaction |
| `EventHistory` | the chain |
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
`EventHistory` at a point and `replay` it. That costs nothing because
`apply` builds state from nothing. State that changed in place would
need a reverse operation for every kind of event.

## The types

Sixteen types are agreed. Each one below says what it is and why it
exists.

**`EntityId`** — Uniquely identifies an entity

**`EventId`** — the position of one event in the `EventHistory`.

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
that a person reads, a type, how long it has been here, and its facts.
`existence` is a `TimeSpan`, so the world knows Ada was alive in year 12
and gone by year 50. Where it sits is a fact, not a field — see
decision 32.

**`Fact`** — one thing that is true of an entity RIGHT NOW. The mill is
burned. The treasury holds 4000. Ada is king of Ashford. A fact holds no
time of its own. It points at the event that opened it, and that event
carries the tick and the reason. When a fact ends it leaves the state,
and the `EventHistory` keeps it.

**`Event`** — one thing that happened, at one tick.

**`EventKind`** — the five things that can happen. A closed list, so a
director can never invent a change nobody wrote a rule for.

**`EventHistory`** — every event, in order. Append-only by
construction, with one named method that shortens it, for rollback.

**`World`** — the tick, the vocabulary, the entities, and the history.
The whole thing.

**`Rejection`** — why a proposal was refused. `Malformed` when the
proposal is wrong on its own. `Contradiction` when the world is in the
way.

**`Briefing`** — what the crate hands SandMan. The entities that
matter, as they are now, and a tail of recent events.

**`FactVocabulary`** — every fact name one world knows, and the rules
for each. `validate` refuses a name that is not in it. The same list
goes into a director prompt, so the model chooses from a closed set.

**`FactRules`** — the rules for one name. Is it a number or a flag.
Does it name a second entity. How many links each side allows. Which
entity types are allowed on each end. An enum, so a rule that needs a
target cannot be declared on a name that has none.

**`Count`** — `One`, `Many`, or `AtMost(n)`. It caps each side of a
link. `holders: One` means Ashford has one king. `targets: One` means
Ada has one spouse. `holders: AtMost(12)` means twelve sit on Ashford's
council, and the next city gets its own twelve.

### Where each type lives

| Type | Lives in |
|---|---|
| `Event`, `EventKind`, `EventHistory` | the history |
| `Entity`, `Fact` | the state |
| `FactVocabulary`, `FactRules` | the world, beside both |
| `EntityId`, `EventId`, `Tick`, `TimeSpan`, `EntityType`, `Count` | both |
| `Rejection`, `Briefing` | neither — they cross the boundary to SandMan |

Nothing in the state is an event. A director hands back a PROPOSED
event, so one exists in flight for a moment. Only an accepted one
reaches the history.

## The names

These names are agreed. The shapes below hold ONLY the agreed parts.
Every gap is marked, and a gap is not a hint.

```rust
/// A handle on one entity. Never reused: the history names the dead.
struct EntityId(u32);

/// The position of one event in the EventHistory.
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
    /// Started, and maybe ended. One span, ever.
    existence: TimeSpan,
    /// Everything true of it right now, including where it sits.
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
    Linked {
        numeric: bool,
        holders: Count,
        targets: Count,
        /// holder type => the target types it allows. empty = any.
        allowed: BTreeMap<EntityType, Vec<EntityType>>,
    },
}

/// How many of something one rule allows.
/// `One` is `AtMost(1)`, spelled for the reader.
enum Count { One, Many, AtMost(u16) }

/// One entry in the history.
struct Event { id: EventId, tick: Tick, kind: EventKind }

/// The five things that can happen.
enum EventKind {
    EntityCreated   { id: EntityId, entity_type: EntityType, name: String },
    EntityDestroyed { id: EntityId },
    FactStart  { entity: EntityId, name: String, value: Option<i64>, linked_to: Option<EntityId> },
    FactUpdate { entity: EntityId, name: String, linked_to: Option<EntityId>, from: i64, to: i64 },
    FactEnd    { entity: EntityId, name: String, linked_to: Option<EntityId> },
}

/// Append-only. `truncate` is the one way to shorten it, for rollback.
struct EventHistory(Vec<Event>);

/// The world. The state is built from the history by `apply`.
struct World {
    tick: Tick,
    vocabulary: FactVocabulary,
    entities: BTreeMap<EntityId, Entity>,
    history: EventHistory,
}

/// Why a proposal was refused. Decision 38 holds the variants.
enum Rejection { Malformed(Malformed), Contradiction(Contradiction) }

/// What the crate hands SandMan. Two cuts: relevance, then recency.
struct Briefing { entities: Vec<EntityId>, recent: Vec<EventId> }
```

`existence` keeps its own name. It is a `TimeSpan`, and the word says
what the span is for. It is the only `TimeSpan` left.

## Open

Not decided. Do not build these.

- **One-of-a-kind solo facts.** Only one city is the capital. Decision
  25 caps each side of a LINK, and says nothing about a solo fact that
  only one entity in the world can hold. No consumer has asked.
- **Type rules for a solo fact.** Decision 33 covers linked facts. A
  solo fact has no equivalent, so nothing stops "the sword is burned"
  from being "the faction is burned". No consumer has asked.
- **Walking a fact backwards.** Decision 15 sends an ended fact out of
  the state, so "who was king in year 30" scans the `EventHistory`. The fix
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
  `EventHistory` that never stops. Dropping the old part needs a rolled-up
  state at the cut. Not decided, and not needed for a first world.

  Pruning breaks decision 16. A `Fact` holds `opened: EventId`, and a
  pruned event leaves that pointing at nothing. Any pruning design must
  answer this — most likely by rewriting a surviving fact to point at
  the snapshot.

  It also loses duration for good. Once the opening event is gone,
  nothing knows when the famine started. A snapshot has to carry the
  ticks that the dropped events held, or facts have to gain a
  `since: Tick`.
- **How a `Malformed` gets back into the prompt.** Decision 38 says it
  means the prompt failed. Whether SandMan fixes the prompt by hand, or
  feeds the rejection back as an example, is open.
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
- **How a `Briefing` chooses its entities.** Decision 41 names the two
  cuts. The ranking that fills the first one is decision 28's salience,
  and how it scores is open.
- **How salience is scored.** Decision 28 says the inputs are facts.
  How they rank is open.
- **The rules.** Question 4. Nothing is decided beyond what each
  decision above already forces.

## Build order

Five steps. Each one ends in something that compiles and has a test
that would fail without it. Nothing in "Open" is built.

**1. The types.** `time.rs`, `entity.rs`, `fact.rs`, `event.rs`. Data
and serde only, plus `FactVocabulary` lookup. No `World` yet.

- Every type round-trips through JSON.
- A vocabulary returns the rules for a declared name, and nothing for
  a name nobody declared.
- `TimeSpan::holds_at` answers before, during, and after.

**2. `apply` and `replay`.** `world.rs` and `EventHistory`. The five
events fold into state. No validation — `apply` trusts what it is
given.

- The same history builds the same state, twice (decision 17).
- A fact that ends leaves the state, and the history keeps it.
- `FactUpdate` closes the old value and opens the new one.
- An entity stays in the state after `EntityDestroyed`, with its
  existence closed.

**3. `located_in` and the containment queries.** The crate declares the
name in every vocabulary. `contents`, `ancestry`, and the cycle walk.

- A new vocabulary already holds `located_in`.
- `contents(mill)` finds Ada. `ancestry(ada)` gives the mill, then
  Ashford.
- A move ends the old location and opens the new one.

**4. `validate`.** `Malformed` and `Contradiction`, every variant. This
is the biggest step and the one that earns the crate.

- One test per variant, each proving the exact rejection.
- A refusal carries every reason, not the first (decision 36).
- Good events land while bad ones are refused, in one tick
  (decision 37).
- `FactUpdate` with a stale `from` is refused.
- A cycle is refused.

**5. `brief`.** The two cuts. Ranking waits on salience scoring, so
step 5 takes the newest entities and the last N events, and the
ranking slots in later.

- A briefing holds the present of its entities and a tail of history.
- A budget of 5 returns 5 entities.

After step 5 the core is done. Then spec these four together, because
they interlock: hash-linking, a state root, the back-pointer index, and
salience scoring.

## Formal verification

This crate is unusually easy to verify, and that is not luck. The
spec bans I/O, floats, clocks, randomness, and unordered maps. So
`apply` and `validate` are pure functions over closed enums, and
purity is the precondition every formal tool demands.

### The properties worth proving

1. **Replay determinism (decision 17).** `replay(log)` gives one
   state on any machine. Rust's type system gives most of it free:
   a pure function with no interior mutability cannot vary. The
   residual risks are a stray `HashMap` or a float. A clippy lint
   ban closes both.
2. **The inductive invariants.** This is the prize. The claim:
   every state reachable through `validate` + `apply` keeps the
   rules. Each rule is one theorem of one shape — if the invariant
   holds in S, and `validate(S, e)` passes, then `apply(S, e)`
   keeps it:
   - No target has more holders than its `Count` limit.
   - No holder has more targets than its `Count` limit.
   - The `located_in` graph has no cycle.
   - One open fact per (entity, name).
   - Every `Fact.opened` points inside the history.
   - `TimeSpan.from <= until`, and a dead entity gains no facts.
   - Every link obeys the `allowed` type map.
3. **Rollback correctness.** `truncate(i)` then `replay` equals
   `replay` of the prefix. Near-free by construction, and it IS
   the undo promise.
4. **Rejection completeness (decision 36).** For each rule, when
   an event breaks it, the rejection list contains it. This proves
   "one retry fixes everything" is real.
5. **The CAS rule (33½).** A stale `from` is always refused, and
   an accepted update always lands `to`.

Not verifiable: salience scoring, briefing relevance, and anything
the director does. Those are quality judgments, not invariants.
The hash-link and state-root items in "Open" are the opposite:
once decided, each is a one-line theorem ("equal roots imply equal
states"), and both pair with the determinism proof.

### The tools, by cost

Every tool that fits Rust or the spec, cheap first. The list holds
the poor fits too, so nobody re-litigates them.

| Tool | Cost | What it gives | Fit |
|---|---|---|---|
| proptest | hours | model-based tests: random valid logs, assert every invariant after replay | do this regardless; not formal, catches most bugs first |
| quickcheck | hours | same idea as proptest | poor: weaker shrinking, no strategy composition; proptest covers it |
| cargo-fuzz | hours | coverage-guided fuzzing of serde round-trips and `validate` on raw bytes | narrow: the crate parses nothing but JSON; one harness is enough |
| Kani | days | bounded model checking of the REAL Rust code; a world of 3 entities, 2 names, logs of length 5, checked exhaustively | good: a genuine formal result; `String` and `BTreeMap` need small bounds |
| TLA+ | days | model the SPEC, not the code: the five event kinds and `validate` as a state machine, TLC checks small instances | good: finds design holes before Rust exists |
| Alloy | days | the relational rules alone: `Count`, the `allowed` map, cycles | good: this is Alloy's exact sweet spot |
| MIRAI | days | abstract interpretation over MIR, tag analysis | poor: aimed at taint and panics, not at inductive invariants; project dormant |
| Loom | days | exhaustive interleavings of concurrent code | no fit: the crate is single-threaded by design |
| Prusti | weeks | deductive proofs via Viper annotations | weak: less active than Verus and Creusot, struggles with `String` |
| Creusot | weeks | full deductive proofs of the invariants, unbounded, via Why3 | strong when needed; research-grade effort |
| Verus | weeks | same class as Creusot, SMT-based, its own `Map`/`Seq` model types | strong when needed; the code ports into a dialect |
| Aeneas | weeks | translates the REAL Rust code into pure Lean functions; the Lean proofs hold for every input, with no bound | strong: rungs 1 to 4b are BUILT (`lean/README.md`); the Lean is generated, so it does not drift from the Rust |
| Coq / Lean / Isabelle | months | a hand-written model of the spec plus proofs, or extraction | overkill: the model drifts from the Rust unless someone maintains both |

### The ladder

1. proptest now.
2. One Kani harness for the cardinality and cycle invariants next.
3. TLA+ or Alloy when the ruleset grows past what a reviewer holds
   in one head.
4. Verus or Creusot only when the shared game-server world makes a
   state divergence expensive.
5. Aeneas, one rung at a time. The built rungs are the scalar core,
   the record merge, the world laws, the rules inside `apply`, the
   band law, the direction law, the count laws, and the ring law.
   `lean/README.md` holds the rungs and the
   map of the code that does not translate yet.

## Built past the decisions

Each item below is code that the decisions above do not hold. The
first consumer forced most of them: the memory of a roguelike
between runs, on the `Game.progress` save path.

1. **`Solo { numeric: bool }` became `Solo(Shape)`.** A bool says
   that a name takes a number. It says nothing about WHICH
   numbers, or WHICH WAY they move. `Shape` is the same enum
   argument as decision 23, one level down:

   ```rust
   enum Shape {
       Flag   { direction: Direction },
       Number { band: Band, direction: Direction },
   }
   ```

   A band on a flag is nonsense, so a flag cannot declare one.
   `Linked` takes a `Shape` too, in place of its `numeric` bool.
2. **A band caps every number.** `Band { min, max }`, closed at
   both ends. A number outside it is `Malformed::OutOfBand`.
3. **A direction is a law.** `Up`, `Down`, or `Free`. A best
   depth never falls. An unlock never ends. The direction rules
   the life of the fact as well as its number, because ending an
   `Up` fact loses what it remembers.
4. **A memory record, and a merge with five laws.** `Record` is
   the flat cut of one entity: its solo facts, in the JSON shape
   the player scope already stores. `merge` joins two records. It
   is commutative, associative, and idempotent, an empty record
   is its start, and it never moves a field backward. The five
   hold because the join of one field starts from ABSENT, which
   is why the crate needs no default for a new name.
5. **A schema that grows.** `migrate` runs three laws: additive
   only, the rules of a declared name never change, and the
   version steps by one. So `FactVocabulary` carries a version.

   Law two is not taste. `apply` reads the count on the target
   side when it folds a `FactStart`. Change that count, and an
   old history folds into a NEW state. A widened band is the one
   safe change, because `apply` never reads a band.
6. **`FactStart` closes one slot, and a slot is a name and a
   target together.** Decision 25 says one open fact per entity
   and name. That cannot hold for `hates` with `targets: Many`.
   The crate closes the exact slot, and it closes a whole name
   only when the count on the target side is exactly ONE. Then
   there is one fact to close and no choice about which, which is
   the move of decision 32. A count of twelve leaves a choice, so
   the crate refuses with `TooManyTargets` and guesses nothing.

   The holder side never closes anything. Ending the crown of Ada
   is a change to ANOTHER entity, and one event names one
   subject.
7. **Six rejections more, in each half.** `Malformed` gained
   `OutOfBand`, `Backward`, `UnnamedEntity`, `Unmergeable`, and
   `BrokenVocabulary`. `Contradiction` gained `IdInUse`,
   `NoSuchFact`, `Stale`, `Backward`, `TimeMovedBack`,
   `NoMigrationPath`, and `VersionStep`. Decision 33 and a half
   asks for the stale check and names no variant, so `Stale` is
   that one.
8. **A tick never moves back.** The history is ordered, so
   `validate` refuses an event before the tick of the world.
9. **A `TimeSpan` holds its start and not its end.** An entity
   that dies at tick 50 is alive at 49 and gone at 50.
10. **A link points at the dead. A holder must be alive.**
    Decision 9 says a grudge outlives the person, so a new
    `hates` reaches a dead Ada. The invariant "a dead entity
    gains no facts" covers the holder alone. A `FactEnd` on a
    dead entity passes, because a crown does not outlive the
    king.
11. **A `Faction` sits in a `Place`.** Decision 33 shows three
    lines of the `located_in` type map, and a faction is in none
    of them. Without a line, a faction has no place at all.

Three answers to the "Open" list came out of the build, and each
one is small enough to reverse:

- **`replay` does not validate again.** The history is trusted.
  The migration laws hold the other half: the rules of a declared
  name never change, so an old history always folds the same way.
- **A briefing takes the subject first, then the newest.**
  Salience scoring is still open, and no caller changes when it
  lands.
- **A rejection carries no prose.** `Display` writes a default
  line, and a consumer words it again.

## Rules for this crate

1. Hourglass depends on nothing in `server/`.
2. Nothing goes in until a consumer asks for it.
3. Nothing goes in this file until Eitan agrees to it.
