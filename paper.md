---
title: "AdaStream: Decentralized File Hosting Incentivised via Cardano Ada Payments"
date: \today
author: Alexander Nemish
email: alex.nemish@nishlabs.com
---
## Abstract

An atomic swap of coins for files would enable an open market for content hosting,
in which anyone can monetize their excess bandwidth and data storage capacities,
by serving decentralized multimedia services. Verifiable encryption provides a
theoretical solution, but the computational overhead is too expensive in practice.

The BitStream[@1] protocol proposes a solution to the fair exchange problem using Bitcoin Liquid protocol, and requires OP_CAT re-enabled in Bitcoin script.
Our solution uses Cardano blockchain.
Here we present the bond contract implementation using Cardano Plutus V2 smart contract.

## Introduction

## Bond Contract

```scala
//> using scala 3.3.0
//> using plugin org.scalus:scalus-plugin_3:0.3.0
//> using dep org.scalus:scalus_3:0.3.0
def bondContract(datum: Data, redeemer: Data, scriptContext: Data


```

## References

[1] Robin Linus. BitStream: Decentralized File Hosting Incentivised via
Bitcoin Payments. https://robinlinus.com/bitstream.pdf

Sponsor AdaStream developers: addr1qxwg0u9fpl8dac9rkramkcgzerjsfdlqgkw0q8hy5vwk8tzk5pgcmdpe5jeh92guy4mke4zdmagv228nucldzxv95clqe35r3m