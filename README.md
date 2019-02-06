## Formalizing the Bitcoin Modelling Language (BitML)

Based on:
> Massimo Bartoletti and Roberto Zunino, 2018, January.
> "BitML: a calculus for Bitcoin smart contracts"

# File structure

- Utilities
  + `Lists.agda`: Useful list definitions
    * indexing
    * `≾` relation on lists

- Data
  + `Set'.agda`: Sets from lists and and helpful properties that require decidable equality
    * `⊆` relation on lists
    * set operations `∅, ─, ∪` etc...
    * decidable procedure for `↭`

- `Types.agda`: Basic BitML datatypes (+ decidable equality for them)

- `ExampleSetup.agda`: Setup of hypothetical participants (including an honest one)

- BitML: Contracts and Advertisements
  * `Types.agda`: Types of contracts and advertisements (+ helper functions)
    * `DecidableEquality.agda`: decidable equality for contracts/advertisements
    * `Examples.agda`: Examples of contracts/advertisements

- Semantics
  + Actions: Inherently-typed actions that participants can authorize
    * `Types.agda`: Types of actions
    * `DecidableEquality.agda`: decidable equality for actions
    * `Examples.agda`: Examples of actions

  + Configurations: Inherently-typed configurations, which are the states of our small-step semantics
    * `Types.agda`: Types of configurations
    * `DecidableEquality.agda`: decidable equality for configurations
    * `Examples.agda`: Examples of configurations
    * `Helpers.agda`: Shorthands for constructing configurations + implicit-style operators

  + `InferenceRules.agda`: The semantic rules of the BitML calculus, i.e. small-step semantics through configurations

- `Example.agda`: Example inference for the timed-committement example, see Chapter 2 of the BitML paper.

