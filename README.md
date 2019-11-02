## Formalizing the Bitcoin Modelling Language (BitML) [![Build Status](https://travis-ci.com/omelkonian/formal-bitml.svg?branch=master)](https://travis-ci.com/omelkonian/formal-bitml)

Based on:
> Massimo Bartoletti and Roberto Zunino, 2018, January.
> "BitML: a calculus for Bitcoin smart contracts"

# HTML
Browse the Agda code in HTML [here](http://omelkonian.github.io/formal-bitml).

# File structure

- `BitML.BasicTypes.agda`: Basic BitML datatypes (+ decidable equality for them)

- BitML.Contracts: Contracts and Advertisements
  * `Types.agda`: Types of contracts and advertisements (+ helper functions)
  * `DecidableEquality.agda`: decidable equality for contracts/advertisements
  * `Examples.agda`: Examples of contracts/advertisements

- BitML.Semantics
  + Actions: Inherently-typed actions that participants can authorize
    * `Types.agda`: Types of actions
    * `DecidableEquality.agda`: decidable equality for actions
    * `Examples.agda`: Examples of actions

  + Configurations: Inherently-typed configurations, which are the states of our small-step semantics
    * `Types.agda`: Types of configurations
    * `DecidableEquality.agda`: decidable equality for configurations
    * `Examples.agda`: Examples of configurations
    * `Helpers.agda`: Shorthands for constructing configurations + implicit-style operators

  + Labels: Untyped labels of inference rules
    * `Types.agda`: Types of labels
    * `DecidableEquality.agda`: decidable equality for labels
    * `Examples.agda`: Examples of labels

  + `InferenceRules.agda`: The semantic rules of the BitML calculus, i.e. small-step semantics through configurations

- BitML.Example: Example contract shown in Chapter 2 of the BitML paper
  * `ExampleSetup.agda`: Setup of hypothetical participants (including an honest one)
  * `Example.agda`: Example inference for the timed-committement example

- BitML.SymbolicModel
  * `Strategy.agda`: Defines honest and adversarial strategies
  * `Helpers.agda`: Several helpers for dealing with strategies
  * `Properties.agda`: Meta-theory found in Chapter 5 of the BitML paper
