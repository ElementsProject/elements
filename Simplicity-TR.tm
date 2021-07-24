<TeXmacs|1.99.2>

<style|book>

<\body>
  <\doc-data|<\doc-title>
    Simplicity
  </doc-title>|<doc-author|<author-data|<author-name|Russell
  O'Connor>|<\author-affiliation>
    Blockstream
  </author-affiliation>|<author-email|roconnor@blockstream.com>>>|<doc-misc|DRAFT>|<doc-date|<date>>>
    \;
  </doc-data>

  <\table-of-contents|toc>
    <vspace*|1fn><with|font-series|bold|math-font-series|bold|1<space|2spc>Introduction>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-1><vspace|0.5fn>

    1.1<space|2spc>Bitcoin Script <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-2>

    1.2<space|2spc>Simplicity's Design Goals
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-3>

    <with|par-left|1tab|1.2.1<space|2spc>Static Analysis
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-4>>

    <with|par-left|1tab|1.2.2<space|2spc>Pruning and Sharing
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-5>>

    <with|par-left|1tab|1.2.3<space|2spc>Formal Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-6>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|2<space|2spc>Type
    Theory Preliminaries> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-7><vspace|0.5fn>

    2.1<space|2spc>Algebraic Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-8>

    <with|par-left|1tab|2.1.1<space|2spc>Records
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-9>>

    2.2<space|2spc>Functors <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-10>

    <with|par-left|1tab|2.2.1<space|2spc>Option Functor
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-11>>

    <with|par-left|1tab|2.2.2<space|2spc>List Functors
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-12>>

    2.3<space|2spc>Monads <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-13>

    <with|par-left|1tab|2.3.1<space|2spc>Kleisli Morphisms
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-14>>

    <with|par-left|1tab|2.3.2<space|2spc>Cartesian Strength
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-15>>

    <with|par-left|1tab|2.3.3<space|2spc>Identity Monad
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-16>>

    <with|par-left|1tab|2.3.4<space|2spc>Monad Zero
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-17>>

    <with|par-left|2tab|2.3.4.1<space|2spc>Option Monad
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-18>>

    2.4<space|2spc>Multi-bit Words <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-19>

    <with|par-left|1tab|2.4.1<space|2spc>Byte Strings
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-20>>

    <with|par-left|1tab|2.4.2<space|2spc>Bit Strings
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-21>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|3<space|2spc>Core
    Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-22><vspace|0.5fn>

    3.1<space|2spc>Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-23>

    <with|par-left|1tab|3.1.1<space|2spc>Abstract Syntax
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-24>>

    <with|par-left|1tab|3.1.2<space|2spc>Formal Syntax
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-25>>

    <with|par-left|1tab|3.1.3<space|2spc>Formal Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-26>>

    3.2<space|2spc>Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-27>

    <with|par-left|1tab|3.2.1<space|2spc>Identity
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-28>>

    <with|par-left|1tab|3.2.2<space|2spc>Composition
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-29>>

    <with|par-left|1tab|3.2.3<space|2spc>Constant Unit
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-30>>

    <with|par-left|1tab|3.2.4<space|2spc>Left Injection
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-31>>

    <with|par-left|1tab|3.2.5<space|2spc>Right Injection
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-32>>

    <with|par-left|1tab|3.2.6<space|2spc>Case
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-33>>

    <with|par-left|1tab|3.2.7<space|2spc>Pair
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-34>>

    <with|par-left|1tab|3.2.8<space|2spc>Take
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-35>>

    <with|par-left|1tab|3.2.9<space|2spc>Drop
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-36>>

    <with|par-left|1tab|3.2.10<space|2spc>Formal Syntax
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-37>>

    <with|par-left|1tab|3.2.11<space|2spc>Formal Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-38>>

    3.3<space|2spc>Example Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-39>

    <with|par-left|1tab|3.3.1<space|2spc>Bit Operations
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-40>>

    <with|par-left|1tab|3.3.2<space|2spc>Simplicity Notation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-41>>

    <with|par-left|1tab|3.3.3<space|2spc>Generic Equality
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-42>>

    <with|par-left|1tab|3.3.4<space|2spc>Arithmetic
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-43>>

    <with|par-left|1tab|3.3.5<space|2spc>Bitwise Operations
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-44>>

    <with|par-left|1tab|3.3.6<space|2spc>SHA-256
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-45>>

    <with|par-left|2tab|3.3.6.1<space|2spc>Tagged Hashes
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-46>>

    <with|par-left|1tab|3.3.7<space|2spc>Elliptic Curve Operations on
    secp256k1 <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-47>>

    <with|par-left|2tab|3.3.7.1<space|2spc>libsecp256k1
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-48>>

    <with|par-left|2tab|3.3.7.2<space|2spc>libsecp256k1 in Simplicity
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-49>>

    <with|par-left|2tab|3.3.7.3<space|2spc>Schnorr Signature Validation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-50>>

    3.4<space|2spc>Completeness Theorem <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-51>

    3.5<space|2spc>Operational Semantics <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-52>

    <with|par-left|1tab|3.5.1<space|2spc>Representing Values as Cell Arrays
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-53>>

    <with|par-left|1tab|3.5.2<space|2spc>Bit Machine
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-54>>

    <with|par-left|2tab|3.5.2.1<space|2spc>Frame Instructions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-56>>

    <with|par-left|2tab|3.5.2.2<space|2spc>Active Write Frame Instructions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-57>>

    <with|par-left|2tab|3.5.2.3<space|2spc>Active Read Frame Instructions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-58>>

    <with|par-left|2tab|3.5.2.4<space|2spc>Abort Instruction
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-59>>

    <with|par-left|2tab|3.5.2.5<space|2spc>Bit Machine Programs
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-60>>

    <with|par-left|2tab|3.5.2.6<space|2spc>Crashing the Bit Machine
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-61>>

    <with|par-left|1tab|3.5.3<space|2spc>Executing Simplicity
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-62>>

    <with|par-left|2tab|3.5.3.1<space|2spc>Tail Composition Optimisation
    (TCO) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-63>>

    3.6<space|2spc>Static Analysis <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-64>

    <with|par-left|1tab|3.6.1<space|2spc>Space Resources
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-65>>

    <with|par-left|2tab|3.6.1.1<space|2spc>Maximum Cell Count Bound
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-66>>

    <with|par-left|2tab|3.6.1.2<space|2spc>Maximum Frame Count Bound
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-67>>

    <with|par-left|1tab|3.6.2<space|2spc>Time Resources
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-68>>

    3.7<space|2spc>Commitment Merkle Root
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-69>

    3.8<space|2spc>Type Merkle Root <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-70>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|4<space|2spc>Simplicity
    Extensions> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-71><vspace|0.5fn>

    4.1<space|2spc>Monadic Semantics <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-72>

    4.2<space|2spc>Witness <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-73>

    <with|par-left|1tab|4.2.1<space|2spc>Elided Computation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-74>>

    <with|par-left|1tab|4.2.2<space|2spc>Type Inference with Witness
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-75>>

    4.3<space|2spc>Assertions and Failure
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-76>

    <with|par-left|1tab|4.3.1<space|2spc>Denotational Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-77>>

    <with|par-left|1tab|4.3.2<space|2spc>Merkle Roots
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-78>>

    <with|par-left|2tab|4.3.2.1<space|2spc>Pruning Unused
    <with|font-family|ss|case> Branches <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-79>>

    <with|par-left|2tab|4.3.2.2<space|2spc>Salted Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-80>>

    4.4<space|2spc>Blockchain Primitives <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-81>

    <with|par-left|1tab|4.4.1<space|2spc>Bitcoin Transactions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-82>>

    <with|par-left|2tab|4.4.1.1<space|2spc>Denotational Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-83>>

    <with|par-left|2tab|4.4.1.2<space|2spc>Merkle Roots
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-84>>

    4.5<space|2spc>Simplicity Programs <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-85>

    <with|par-left|1tab|4.5.1<space|2spc>Example:
    <rigid|<with|mode|text|<with|font-family|ss|font-shape|right|checkSigHashAll>>>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-86>>

    4.6<space|2spc>Schnorr Signature Aggregation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-87>

    4.7<space|2spc>Malleability <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-88>

    <with|par-left|1tab|4.7.1<space|2spc>Transaction Weight
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-89>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|5<space|2spc>Jets>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-90><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|6<space|2spc>Delegation>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-91><vspace|0.5fn>

    6.1<space|2spc>Implementing <with|font-family|ss|disconnect> on the Bit
    Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-92>

    <with|par-left|1tab|6.1.1<space|2spc>Static Analysis of
    <with|font-family|ss|disconnect> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-93>>

    <with|par-left|2tab|6.1.1.1<space|2spc>Space Resources
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-94>>

    6.2<space|2spc>Unbounded Loops <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-95>

    <with|par-left|1tab|6.2.1<space|2spc>Adding a <with|font-family|ss|loop>
    primitive to Simplicity? <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-96>>

    6.3<space|2spc>Universal Signature Hash Modes
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-97>

    <with|par-left|1tab|6.3.1<space|2spc>Side-Effects and Delegation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-98>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|7<space|2spc>Type
    Inference and Serialization> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-99><vspace|0.5fn>

    7.1<space|2spc>Explicit Simplicity DAGs
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-100>

    <with|par-left|1tab|7.1.1<space|2spc>Type Inference
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-101>>

    <with|par-left|1tab|7.1.2<space|2spc>Reconstructing Simplicity
    Expressions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-102>>

    <with|par-left|2tab|7.1.2.1<space|2spc>syncase
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-103>>

    <with|par-left|2tab|7.1.2.2<space|2spc>inflate
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-104>>

    7.2<space|2spc>Serialization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-105>

    <with|par-left|1tab|7.2.1<space|2spc>Serialization of Bit Strings and
    Positive Numbers <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-106>>

    <with|par-left|1tab|7.2.2<space|2spc>Serialization of Simplicity
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-107>>

    <with|par-left|1tab|7.2.3<space|2spc>Identity Merkle Root
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-108>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|8<space|2spc>Coq
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-109><vspace|0.5fn>

    8.1<space|2spc>Simplicity Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-110>

    8.2<space|2spc>Simplicity Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-111>

    <with|par-left|1tab|8.2.1<space|2spc>The ``Initial'' Representation of
    Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-112>>

    <with|par-left|1tab|8.2.2<space|2spc>The ``Final'' Representation of
    Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-113>>

    <with|par-left|2tab|8.2.2.1<space|2spc>Simplicity Algebras
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-114>>

    <with|par-left|2tab|8.2.2.2<space|2spc>The ``Final'' Representation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-115>>

    <with|par-left|2tab|8.2.2.3<space|2spc>Constructing ``Final'' Terms
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-116>>

    <with|par-left|1tab|8.2.3<space|2spc>Why two representations of Terms?
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-117>>

    8.3<space|2spc>Example Simplicity Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-118>

    <with|par-left|1tab|8.3.1<space|2spc>Bits
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-119>>

    <with|par-left|1tab|8.3.2<space|2spc>Arithmetic
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-120>>

    <with|par-left|1tab|8.3.3<space|2spc>SHA256
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-121>>

    8.4<space|2spc>The Hierarchy of Simplicity Language Extensions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-122>

    <with|par-left|1tab|8.4.1<space|2spc>Witness
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-124>>

    <with|par-left|1tab|8.4.2<space|2spc>Assertion
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-125>>

    <with|par-left|1tab|8.4.3<space|2spc>Delegation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-126>>

    <with|par-left|1tab|8.4.4<space|2spc>Primitives
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-127>>

    <with|par-left|2tab|8.4.4.1<space|2spc>Bitcoin
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-128>>

    <with|par-left|1tab|8.4.5<space|2spc>Jets
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-129>>

    <with|par-left|1tab|8.4.6<space|2spc>Full Simplicity
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-130>>

    8.5<space|2spc>Merkle Roots <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-131>

    8.6<space|2spc>The Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-132>

    <with|par-left|1tab|8.6.1<space|2spc>Bit Machine Code
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-133>>

    <with|par-left|2tab|8.6.1.1<space|2spc>Bit Machine Programs
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-134>>

    <with|par-left|1tab|8.6.2<space|2spc>Translating Simplicity to the Bit
    Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-135>>

    <with|par-left|1tab|8.6.3<space|2spc>Static Analysis
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-136>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|9<space|2spc>Haskell
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-137><vspace|0.5fn>

    9.1<space|2spc><with|font-family|tt|language|verbatim|Simplicity-Core>
    library <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-138>

    <with|par-left|1tab|9.1.1<space|2spc>Simplicity Types
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-139>>

    <with|par-left|1tab|9.1.2<space|2spc>Simplicity Terms
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-140>>

    <with|par-left|1tab|9.1.3<space|2spc>Merkle Roots
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-141>>

    <with|par-left|1tab|9.1.4<space|2spc>Tensors
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-142>>

    <with|par-left|1tab|9.1.5<space|2spc>Example Simplicity Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-143>>

    <with|par-left|2tab|9.1.5.1<space|2spc>Generic
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-144>>

    <with|par-left|2tab|9.1.5.2<space|2spc>Bits
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-145>>

    <with|par-left|2tab|9.1.5.3<space|2spc>Multi-bit Words
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-146>>

    <with|par-left|2tab|9.1.5.4<space|2spc>Arithmetic
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-147>>

    <with|par-left|2tab|9.1.5.5<space|2spc>Loop
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-148>>

    <with|par-left|1tab|9.1.6<space|2spc>Libraries of Simplicity Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-149>>

    <with|par-left|2tab|9.1.6.1<space|2spc>SHA-256
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-150>>

    <with|par-left|2tab|9.1.6.2<space|2spc>LibSecp256k1
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-151>>

    <with|par-left|2tab|9.1.6.3<space|2spc>CheckSigHash
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-152>>

    <with|par-left|1tab|9.1.7<space|2spc>The Bit Machine
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-153>>

    <with|par-left|2tab|9.1.7.1<space|2spc>Translating Simplicity to the Bit
    Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-154>>

    <with|par-left|2tab|9.1.7.2<space|2spc>Static Analysis
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-155>>

    <with|par-left|2tab|9.1.7.3<space|2spc>Fast Evaluation with FFI
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-156>>

    9.2<space|2spc><with|font-family|tt|language|verbatim|Simplicity-Indef>
    library <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-157>

    <with|par-left|1tab|9.2.1<space|2spc>Primitive Signature
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-158>>

    <with|par-left|1tab|9.2.2<space|2spc>Primitive Terms
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-159>>

    <with|par-left|1tab|9.2.3<space|2spc><with|font-family|tt|language|verbatim|JetType>
    class <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-160>>

    <with|par-left|1tab|9.2.4<space|2spc>Denotational Semantics of Full
    Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-161>>

    <with|par-left|1tab|9.2.5<space|2spc>Type Inference
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-162>>

    <with|par-left|1tab|9.2.6<space|2spc>Serialization
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-163>>

    <with|par-left|2tab|9.2.6.1<space|2spc>Free Monadic Deserializaiton
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-164>>

    <with|par-left|2tab|9.2.6.2<space|2spc>Serialization of Simplicity DAGs
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-165>>

    <with|par-left|1tab|9.2.7<space|2spc>Jet Substitution
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-166>>

    9.3<space|2spc><with|font-family|tt|language|verbatim|Simplicity-Bitcoin>
    Libary <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-167>

    9.4<space|2spc><with|font-family|tt|language|verbatim|Simplicity> Library
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-168>

    <with|par-left|1tab|9.4.1<space|2spc>CheckSigHashAll
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-169>>

    <with|par-left|1tab|9.4.2<space|2spc>Known Discounted Jets
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-170>>

    9.5<space|2spc>Simplicity <with|font-family|tt|language|verbatim|testsuite>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-171>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|10<space|2spc>C
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-172><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|Appendix
    A<space|2spc>Elements Application> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-173><vspace|0.5fn>

    A.1<space|2spc>Denotational Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-174>

    <with|par-left|1tab|A.1.1<space|2spc>Null Data
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-175>>

    <with|par-left|1tab|A.1.2<space|2spc>Merkle Roots
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-176>>

    <with|par-left|1tab|A.1.3<space|2spc>Serialization
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-177>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|Appendix
    B<space|2spc>Catelogue of Jets> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-178><vspace|0.5fn>

    B.1<space|2spc><with|font-family|tt|language|verbatim|110...: >Core Jets
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-179>

    <with|par-left|1tab|B.1.1<space|2spc><with|font-family|tt|language|verbatim|1100...:
    >Jets for multi-bit logic <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-180>>

    <with|par-left|2tab|B.1.1.1<space|2spc><with|font-family|ss|low>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-181>>

    <with|par-left|2tab|B.1.1.2<space|2spc><with|font-family|ss|high>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-182>>

    <with|par-left|2tab|B.1.1.3<space|2spc><with|font-family|ss|complement>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-183>>

    <with|par-left|2tab|B.1.1.4<space|2spc><with|font-family|ss|and>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-184>>

    <with|par-left|2tab|B.1.1.5<space|2spc><with|font-family|ss|or>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-185>>

    <with|par-left|2tab|B.1.1.6<space|2spc><with|font-family|ss|xor>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-186>>

    <with|par-left|2tab|B.1.1.7<space|2spc><with|font-family|ss|maj>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-187>>

    <with|par-left|2tab|B.1.1.8<space|2spc><with|font-family|ss|xor3>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-188>>

    <with|par-left|2tab|B.1.1.9<space|2spc><with|font-family|ss|ch>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-189>>

    <with|par-left|2tab|B.1.1.10<space|2spc><with|font-family|ss|some>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-190>>

    <with|par-left|2tab|B.1.1.11<space|2spc><with|font-family|ss|all>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-191>>

    <with|par-left|2tab|B.1.1.12<space|2spc><with|font-family|ss|eq>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-192>>

    <with|par-left|2tab|B.1.1.13<space|2spc><with|font-family|ss|full-left-shift>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-193>>

    <with|par-left|2tab|B.1.1.14<space|2spc><with|font-family|ss|full-right-shift>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-194>>

    <with|par-left|2tab|B.1.1.15<space|2spc><with|font-family|ss|leftmost>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-195>>

    <with|par-left|2tab|B.1.1.16<space|2spc><with|font-family|ss|rightmost>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-196>>

    <with|par-left|2tab|B.1.1.17<space|2spc><with|font-family|ss|left-pad-low>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-197>>

    <with|par-left|2tab|B.1.1.18<space|2spc><with|font-family|ss|left-pad-high>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-198>>

    <with|par-left|2tab|B.1.1.19<space|2spc><with|font-family|ss|left-extend>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-199>>

    <with|par-left|2tab|B.1.1.20<space|2spc><with|font-family|ss|right-pad-low>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-200>>

    <with|par-left|2tab|B.1.1.21<space|2spc><with|font-family|ss|right-pad-high>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-201>>

    <with|par-left|2tab|B.1.1.22<space|2spc><with|font-family|ss|right-extend>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-202>>

    <with|par-left|2tab|B.1.1.23<space|2spc><with|font-family|ss|right-shift-with>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-203>>

    <with|par-left|2tab|B.1.1.24<space|2spc><with|font-family|ss|right-shift>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-204>>

    <with|par-left|2tab|B.1.1.25<space|2spc><with|font-family|ss|right-rotate>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-205>>

    <with|par-left|2tab|B.1.1.26<space|2spc><with|font-family|ss|transpose>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-206>>

    <with|par-left|2tab|B.1.1.27<space|2spc><with|font-family|ss|find-first-high>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-207>>

    <with|par-left|2tab|B.1.1.28<space|2spc><with|font-family|ss|find-last-high>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-208>>

    <with|par-left|2tab|B.1.1.29<space|2spc><with|font-family|ss|bit>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-209>>

    <with|par-left|1tab|B.1.2<space|2spc><with|font-family|tt|language|verbatim|110100...:
    >Jets for arithmetic <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-210>>

    <with|par-left|2tab|B.1.2.1<space|2spc><with|font-family|ss|one>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-211>>

    <with|par-left|2tab|B.1.2.2<space|2spc><with|font-family|ss|full-add>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-212>>

    <with|par-left|2tab|B.1.2.3<space|2spc><with|font-family|ss|add>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-213>>

    <with|par-left|2tab|B.1.2.4<space|2spc><with|font-family|ss|full-increment>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-214>>

    <with|par-left|2tab|B.1.2.5<space|2spc><with|font-family|ss|increment>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-215>>

    <with|par-left|2tab|B.1.2.6<space|2spc><with|font-family|ss|popcount>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-216>>

    <with|par-left|2tab|B.1.2.7<space|2spc><with|font-family|ss|full-subtract>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-217>>

    <with|par-left|2tab|B.1.2.8<space|2spc><with|font-family|ss|subtract>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-218>>

    <with|par-left|2tab|B.1.2.9<space|2spc><with|font-family|ss|negate>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-219>>

    <with|par-left|2tab|B.1.2.10<space|2spc><with|font-family|ss|full-decrement>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-220>>

    <with|par-left|2tab|B.1.2.11<space|2spc><with|font-family|ss|decrement>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-221>>

    <with|par-left|2tab|B.1.2.12<space|2spc><with|font-family|ss|full-multiply>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-222>>

    <with|par-left|2tab|B.1.2.13<space|2spc><with|font-family|ss|multiply>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-223>>

    <with|par-left|2tab|B.1.2.14<space|2spc><with|font-family|tt|language|verbatim|><with|font-family|ss|is-zero>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-224>>

    <with|par-left|2tab|B.1.2.15<space|2spc><with|font-family|tt|language|verbatim|><with|font-family|ss|is-one>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-225>>

    <with|par-left|2tab|B.1.2.16<space|2spc><with|font-family|ss|le>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-226>>

    <with|par-left|2tab|B.1.2.17<space|2spc><with|font-family|ss|lt>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-227>>

    <with|par-left|2tab|B.1.2.18<space|2spc><with|font-family|ss|min>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-228>>

    <with|par-left|2tab|B.1.2.19<space|2spc><with|font-family|ss|max>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-229>>

    <with|par-left|2tab|B.1.2.20<space|2spc><with|font-family|ss|median>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-230>>

    <with|par-left|2tab|B.1.2.21<space|2spc><with|font-family|ss|div2n1n>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-231>>

    <with|par-left|2tab|B.1.2.22<space|2spc><with|font-family|ss|div-mod>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-232>>

    <with|par-left|2tab|B.1.2.23<space|2spc><with|font-family|ss|divide>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-233>>

    <with|par-left|2tab|B.1.2.24<space|2spc><with|font-family|ss|modulo>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-234>>

    <with|par-left|2tab|B.1.2.25<space|2spc><with|font-family|ss|divides>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-235>>

    <with|par-left|2tab|B.1.2.26<space|2spc><with|font-family|ss|eea>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-236>>

    <with|par-left|2tab|B.1.2.27<space|2spc><with|font-family|ss|bezout>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-237>>

    <with|par-left|2tab|B.1.2.28<space|2spc><with|font-family|ss|gcd>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-238>>

    <with|par-left|2tab|B.1.2.29<space|2spc><with|font-family|ss|cofactors>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-239>>

    <with|par-left|2tab|B.1.2.30<space|2spc><with|font-family|ss|lcm>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-240>>

    <with|par-left|2tab|B.1.2.31<space|2spc><with|font-family|ss|jacobi>
    (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-241>>

    <with|par-left|2tab|B.1.2.32<space|2spc><with|font-family|ss|absolute-value>
    (signed input/unsigned output) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-242>>

    <with|par-left|2tab|B.1.2.33<space|2spc><with|font-family|tt|language|verbatim|><with|font-family|ss|sign>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-243>>

    <with|par-left|2tab|B.1.2.34<space|2spc><with|font-family|ss|signed-le>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-244>>

    <with|par-left|2tab|B.1.2.35<space|2spc><with|font-family|ss|signed-lt>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-245>>

    <with|par-left|2tab|B.1.2.36<space|2spc><with|font-family|ss|signed-min>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-246>>

    <with|par-left|2tab|B.1.2.37<space|2spc><with|font-family|ss|signed-max>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-247>>

    <with|par-left|2tab|B.1.2.38<space|2spc><with|font-family|ss|signed-median>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-248>>

    <with|par-left|2tab|B.1.2.39<space|2spc><with|font-family|ss|signed-right-shift>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-249>>

    <with|par-left|2tab|B.1.2.40<space|2spc><with|font-family|ss|signed-divmod>
    (unsigned denominator) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-250>>

    <with|par-left|2tab|B.1.2.41<space|2spc><with|font-family|ss|signed-div>
    (unsigned denominator) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-251>>

    <with|par-left|2tab|B.1.2.42<space|2spc><with|font-family|ss|signed-signed-divmod>
    (signed denominator) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-252>>

    <with|par-left|2tab|B.1.2.43<space|2spc><with|font-family|ss|signed-signed-div>
    (signed denominator) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-253>>

    <with|par-left|1tab|B.1.3<space|2spc><with|font-family|tt|language|verbatim|110101...:
    >Jets for hash functions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-254>>

    <with|par-left|2tab|B.1.3.1<space|2spc><with|font-family|tt|language|verbatim|1101010...:
    >Jets for SHA-2 <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-255>>

    <with|par-left|4tab|<with|font-family|ss|sha-256-block>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-256><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|sha-256-iv>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-257><vspace|0.15fn>>

    <with|par-left|2tab|B.1.3.2<space|2spc><with|font-family|tt|language|verbatim|110101100...:
    >Jets for SHA-3 <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-258>>

    <with|par-left|4tab|<with|font-family|ss|sha3-zero>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-259><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|sha3-absorb>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-260><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|sha3-xor>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-261><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|sha3-permute>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-262><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|sha3-squeeze-256>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-263><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|sha3-squeeze-512>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-264><vspace|0.15fn>>

    <with|par-left|2tab|B.1.3.3<space|2spc><with|font-family|tt|language|verbatim|110101101...:
    >Jets for RIPEMD <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-265>>

    <with|par-left|2tab|B.1.3.4<space|2spc><with|font-family|tt|language|verbatim|110101110000...:
    >Jets for SHA-1 (RESERVED) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-266>>

    <with|par-left|1tab|B.1.4<space|2spc><with|font-family|tt|language|verbatim|110110000...:
    >Jets for elliptic curve functions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-267>>

    <with|par-left|2tab|B.1.4.1<space|2spc><with|font-family|tt|language|verbatim|1101100000...:
    >Jets for secp256k1 <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-268>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-point-verify>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-269><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-decompress>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-270><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-linear-verify>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-271><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-linear-combination>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-272><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-scale>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-273><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-generate>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-274><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-infinity>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-275><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-normalize>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-276><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-negate>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-277><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-ge-negate>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-278><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-double>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-279><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-add>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-280><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-ge-add-ex>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-281><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-ge-add>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-282><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-is-infinity>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-283><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-equiv>
    <with|color|red|Does not exist in libsecp256k1>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-284><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-ge-equiv>
    <with|color|red|Does not exist in libsecp256k1>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-285><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-x-equiv>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-286><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-y-is-odd>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-287><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-is-on-curve>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-288><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-ge-is-on-curve>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-289><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-scalar-normalize>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-290><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-scalar-negate>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-291><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-scalar-add>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-292><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-scalar-square>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-293><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-scalar-multiply>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-294><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-scalar-multiply-lambda>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-295><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-scalar-invert>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-296><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-scalar-is-zero>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-297><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-ge-scale-lambda>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-298><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-gej-scale-lambda>
    <with|color|red|Consider removing> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-299><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-scalar-split-lambda>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-300><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-short-scalar>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-301><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-fe-normalize>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-302><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-fe-negate>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-303><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-fe-add>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-304><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-fe-square>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-305><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-fe-multiply>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-306><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-fe-multiply-beta>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-307><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-fe-invert>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-308><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-fe-square-root>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-309><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-fe-is-zero>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-310><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-fe-is-odd>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-311><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-fe-is-quad>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-312><vspace|0.15fn>>

    <with|par-left|1tab|B.1.5<space|2spc><with|font-family|tt|language|verbatim|110110001...:
    >Jets for digital signatures <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-313>>

    <with|par-left|2tab|B.1.5.1<space|2spc><with|font-family|tt|language|verbatim|1101100010...:
    >Jets for secp256k1 based digital signatures
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-314>>

    <with|par-left|4tab|<with|font-family|ss|bip0340-schnorr-verify>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-315><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|bip0340-challenge-iv>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-316><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|bip0340-challenge-midstate>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-317><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-signature-unpack>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-318><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-pubkey-unpack>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-319><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-pubkey-unpack-neg>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-320><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|secp256k1-ecdsa>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-321><vspace|0.15fn>>

    <with|par-left|1tab|B.1.6<space|2spc><with|font-family|tt|language|verbatim|110110010...:
    >Jets for Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-322>>

    <with|par-left|2tab|B.1.6.1<space|2spc><with|font-family|tt|language|verbatim|11011000100...:
    >Jets for tagged hash IVs <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-323>>

    <with|par-left|4tab|<with|font-family|ss|iden-commitment-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-324><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|comp-commitment-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-325><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|unit-commitment-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-326><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|injl-commitment-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-327><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|injr-commitment-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-328><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|case-commitment-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-329><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|pair-commitment-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-330><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|take-commitment-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-331><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|drop-commitment-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-332><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|witness-commitment-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-333><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|disconnect-commitment-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-334><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|fail-commitment-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-335><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|signtaure-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-336><vspace|0.15fn>>

    <with|par-left|4tab|<with|font-family|ss|sighash-tag>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-337><vspace|0.15fn>>

    <with|par-left|1tab|B.1.7<space|2spc><with|font-family|tt|language|verbatim|110110011...:
    >Jets for Bitcoin (without primitives)
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-338>>

    <with|par-left|2tab|B.1.7.1<space|2spc><with|font-family|ss|parse-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-339>>

    <with|par-left|2tab|B.1.7.2<space|2spc><with|font-family|ss|parse-sequence>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-340>>

    <with|par-left|1tab|B.1.8<space|2spc><with|font-family|tt|language|verbatim|1101101000...:
    >Jets for Elements (without primitives)
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-341>>

    <with|par-left|2tab|B.1.8.1<space|2spc><with|font-family|ss|generate-entropy>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-342>>

    <with|par-left|2tab|B.1.8.2<space|2spc><with|font-family|ss|calculate-asset>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-343>>

    <with|par-left|2tab|B.1.8.3<space|2spc><with|font-family|ss|calculate-token>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-344>>

    B.2<space|2spc><with|font-family|tt|language|verbatim|111...: >Bitcoin
    Jets <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-345>

    <with|par-left|1tab|B.2.1<space|2spc>Transaction
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-346>>

    <with|par-left|1tab|B.2.2<space|2spc>Signature Hash Modes
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-347>>

    <with|par-left|1tab|B.2.3<space|2spc>Time Locks
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-348>>

    <with|par-left|2tab|B.2.3.1<space|2spc><with|font-family|ss|total-height-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-349>>

    <with|par-left|2tab|B.2.3.2<space|2spc><with|font-family|ss|total-time-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-350>>

    <with|par-left|2tab|B.2.3.3<space|2spc><with|font-family|ss|total-distance-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-351>>

    <with|par-left|2tab|B.2.3.4<space|2spc><with|font-family|ss|total-duration-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-352>>

    <with|par-left|2tab|B.2.3.5<space|2spc><with|font-family|ss|is-final>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-353>>

    <with|par-left|2tab|B.2.3.6<space|2spc><with|font-family|ss|current-height-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-354>>

    <with|par-left|2tab|B.2.3.7<space|2spc><with|font-family|ss|current-time-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-355>>

    <with|par-left|2tab|B.2.3.8<space|2spc><with|font-family|ss|current-distance-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-356>>

    <with|par-left|2tab|B.2.3.9<space|2spc><with|font-family|ss|current-duration-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-357>>

    <with|par-left|2tab|B.2.3.10<space|2spc><with|font-family|ss|current-is-Final>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-358>>

    <with|par-left|2tab|B.2.3.11<space|2spc><with|font-family|ss|input-height-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-359>>

    <with|par-left|2tab|B.2.3.12<space|2spc><with|font-family|ss|input-time-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-360>>

    <with|par-left|2tab|B.2.3.13<space|2spc><with|font-family|ss|input-distance-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-361>>

    <with|par-left|2tab|B.2.3.14<space|2spc><with|font-family|ss|input-duration-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-362>>

    <with|par-left|2tab|B.2.3.15<space|2spc><with|font-family|ss|input-is-final>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-363>>

    B.3<space|2spc><with|font-family|tt|language|verbatim|111...: >Elements
    Jets <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-364>

    <with|par-left|1tab|B.3.1<space|2spc>Transaction
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-365>>

    <with|par-left|1tab|B.3.2<space|2spc>Time Locks
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-366>>

    <with|par-left|2tab|B.3.2.1<space|2spc><with|font-family|ss|total-height-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-367>>

    <with|par-left|2tab|B.3.2.2<space|2spc><with|font-family|ss|total-time-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-368>>

    <with|par-left|2tab|B.3.2.3<space|2spc><with|font-family|ss|total-distance-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-369>>

    <with|par-left|2tab|B.3.2.4<space|2spc><with|font-family|ss|total-duration-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-370>>

    <with|par-left|2tab|B.3.2.5<space|2spc><with|font-family|ss|is-final>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-371>>

    <with|par-left|2tab|B.3.2.6<space|2spc><with|font-family|ss|current-height-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-372>>

    <with|par-left|2tab|B.3.2.7<space|2spc><with|font-family|ss|current-time-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-373>>

    <with|par-left|2tab|B.3.2.8<space|2spc><with|font-family|ss|current-distance-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-374>>

    <with|par-left|2tab|B.3.2.9<space|2spc><with|font-family|ss|current-duration-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-375>>

    <with|par-left|2tab|B.3.2.10<space|2spc><with|font-family|ss|current-is-Final>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-376>>

    <with|par-left|2tab|B.3.2.11<space|2spc><with|font-family|ss|input-height-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-377>>

    <with|par-left|2tab|B.3.2.12<space|2spc><with|font-family|ss|input-time-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-378>>

    <with|par-left|2tab|B.3.2.13<space|2spc><with|font-family|ss|input-distance-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-379>>

    <with|par-left|2tab|B.3.2.14<space|2spc><with|font-family|ss|input-duration-lock>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-380>>

    <with|par-left|2tab|B.3.2.15<space|2spc><with|font-family|ss|input-is-final>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-381>>

    <with|par-left|1tab|B.3.3<space|2spc>Issuance
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-382>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|Appendix
    C<space|2spc>Alternative Serialization of Simplicity DAGs>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-383><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|Bibliography>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-384><vspace|0.5fn>
  </table-of-contents>

  <chapter|Introduction>

  <section|Bitcoin Script>

  Bitcoin<cite|bitcoin> was the first protocol that used a blockchain to
  build a distributed ledger that allows anyone to transact a cryptographic
  currency with minimal risk of their transaction being reversed or undone,
  and without relying on a trusted third party or central authority.
  Typically access to funds are controlled by a cryptographic private key.
  References to one or more of these funds, which may or may not have the
  same private keys, are assembled into a data structure, called a
  <dfn|transaction>, along with a set of one or more outputs which specify
  which cryptographic public keys that will control each output. This
  transaction data is signed with each private key for each input and added
  to the transaction as <dfn|witness data>.

  More precisely, the outputs are not necessarily controlled by a simple
  single cryptographic key, rather each output is controlled by a small
  program written in a language called <dfn|Bitcoin
  Script><cite|satoshiScript|script>. Bitcoin Script is a stack-based
  language with conditionals operations for control flow and no loops.
  Bitcoin has stack manipulation operations, Boolean logic operations, and
  very simple arithmetic operations (without even multiplication). It also
  has some cryptographic operations that include cryptographic hash
  functions, and digital signature verification operations. The
  <verbatim|CHECKSIG> operation does an ECDSA digital signature verification
  of transaction data.

  A basic example of a Bitcoin Script program pushes an ECDSA public key onto
  the stack, followed by a <verbatim|CHECKSIG> operation. This Script is part
  of the output data within a transaction. In order to spend the funds held
  by such an output, one builds a transaction with an input referencing this
  output and adds a ECDSA signature to the transaction's witness data for the
  input (called a ScriptSig). The witness data describes which part of the
  transaction data is being signed (typically everything other than the
  witness data itself) and has the signature.

  To validate an input, the witness data is pushed onto the stack, and the
  the program in the referenced output is executed. In our example above, the
  program pushes a specific ECDSA public key onto the stack and then executes
  <verbatim|CHECKSIG>. The <verbatim|CHECKSIG> operation pops the public key
  and the signature data off the stack. Then it cryptographically hashes the
  transaction data as specified by the signature data, including which input
  is being signed, and verifies that the digital signature for that public
  key is valid for that hashed data. Only if successful is the value
  <verbatim|1> pushed back onto the stack. In order for a transaction to be
  valid, all inputs are checked in this fashion, by pushing its associated
  witness data onto the stack and then executing the program found in the
  referenced output and requiring a non-zero value be left on the stack.

  From this example, we see that there are three parts that go into checking
  if a transaction's input is authorized to be spent:

  <\itemize-dot>
    <item>A Bitcoin Script, which is contained in a transaction output.

    <item>Witness data, for each transactions input.

    <item>The rest of the transaction data, which includes things like output
    amounts, version numbers, etc.
  </itemize-dot>

  All the data needed to validate a transaction is part of (or
  cryptographically committed within) the transaction data. This means the
  inputs can be validated independently of the state of the rest of the
  blockchain, as far as Bitcoin Script is concerned.

  In the above example, the Bitcoin Script is included into a transaction's
  output, at what I call <dfn|commitment time>. The signature and transaction
  data is specified later at what I call <dfn|redemption time>. That said,
  the Bitcoin Script does not have to be entirely presented at commitment
  time; it is acceptable to just commit to the Bitcoin Script's cryptographic
  hash. Then, at redemption time, the script is revealed together with the
  witness data and the rest of the transaction. In this case the program's
  hash is verified to be equal to the hash committed in the output, and then
  the witness data, and revealed Bitcoin Script are validated as before.
  Bitcoin's <dfn|pay to script hash> (a.k.a. <dfn|P2SH>) follows this
  modified procedure which makes it easy for users to specify complex Bitcoin
  Scripts with to control funds while only needing to provide a single hash
  value to their counterparty when they are first receiving their funds.

  More complex scripts can be devised to do multi-signature, escrow,
  hashed-timelock contracts, etc. However, because of the the limited
  expressiveness of Bitcoin Script (e.g. no multiplication operation), only
  so much can be programmed. Therefore, we want to design an alternative to
  Bitcoin Script that will be more expressive, without sacrificing the good
  properties of Bitcoin Script. We call this new language <dfn|Simplicity>.

  <section|Simplicity's Design Goals>

  Our goals for Simplicity include the following:

  <\itemize-dot>
    <item>Create an expressive language that lets users build novel programs
    and smart contracts.

    <item>Enable useful static analysis to bound computational resource usage
    of programs.

    <item>Minimize bandwidth and storage requirements by allowing sharing of
    expressions and pruning of unused expressions.

    <item>Capture the computational environment entirely within a unit of
    transaction.

    <item>Provide formal semantics for reasoning with off-the-shelf
    proof-assistant software.
  </itemize-dot>

  <subsection|Static Analysis>

  In Bitcoin Script, static analysis lets us count how many operations there
  are and, in particular, bound the maximum number of expensive operations,
  such as signature validation, that could be performed. We can do this
  because Bitcoin Script has no looping operations. In a transaction, if
  Bitcoin Script is deemed to be potentially too expensive from this
  analysis, the program is rejected at redemption time.

  We want to support this same sort of static analysis in Simplicity. It lets
  users determine, at commitment time, the worst case cost for redeeming the
  program, for any possible witness inputs. At redemption time it allows, as
  part of the consensus rules, to bound the cost of running programs prior to
  execution. This serves as one method of avoiding denial of service attacks
  in a blockchain protocol like Bitcoin.

  <subsection|Pruning and Sharing>

  As we saw before at commitment time we only need to specify a cryptographic
  commitment to the program, and the program can be revealed at redemption
  time. For more complex programs with multiple alternative branches, only
  those branches that are actually going to be executed need to be revealed,
  and the remainder of the program that is not executed for this particular
  transaction can be excluded.

  Using a technique called <dfn|Merkelized Abstract Syntax Trees> a.k.a.
  <dfn|MAST>, we can commit to a Merkle root of a program's abstract syntax
  tree. At redemption time, we can prune unused sub-expressions. Instead only
  the Merkle root of the pruned branches need to be revealed in order to
  verify that the program's Merkle root matches the root specified at
  commitment time.

  Because two identical subexpressions necessarily have the same Merkle root,
  this procedure also lets us reduce program size by sharing these identical
  subexpressions. In principle, this sharing could extend as wide as between
  different program in different transactions.

  <subsection|Formal Semantics>

  Once a program has been committed to, it cannot be changed or updated
  later. If a program has errors or security vulnerabilities, it can no
  longer be fixed. Therefore, it is essential to get these program correct.
  Fortunately these programs tend to be relatively small, and hence amenable
  to formal analysis. We use the Coq proof assistant<nbsp><cite|Coq:manual>
  to specify formal semantics of Simplicity. This allows us to both reason
  about programs written in Simplicity, and also lets us reason about our
  static analysis and Simplicity interpreters and prove that they are
  correct.

  While we specifically use the Coq proof assistant, the formal semantics of
  Simplicity is designed to be easy enough to define in any proof assistant,
  especially others based on dependent type theory.

  <chapter|Type Theory Preliminaries><label|chapter:preliminaries>

  <assign|maybe|<math|<math-up|S>>><assign|injl-long|<macro|A|B|x|<math|\<sigma\><rsup|\<b-up-L\>><rsub|<arg|A>,<arg|B>><arg|x>>>><assign|2|<with|font|Bbb*|2>><assign|injr-long|<macro|A|B|x|<math|\<sigma\><rsup|\<b-up-R\>><rsub|<arg|A>,<arg|B>><arg|x>>>><assign|1|<math|<with|font|Bbb*|1>>><assign|pair-long|<macro|x|y|A|B|<math|<around*|\<langle\>|<arg|x>,<arg|y>|\<rangle\>><rsub|<arg|A>,<arg|B>>>>><assign|injl|<macro|x|<math|\<sigma\><rsup|\<b-up-L\>><arg|x>>>><assign|injr|<macro|x|<math|\<sigma\><rsup|\<b-up-R\>><arg|x>>>>In
  this document we endeavour to be precise about the semantics surrounding
  the definition of the Simplicity language. To this end we use formal
  language composed from a mix of mathematics, category theory, simple type
  theory, and functional programming. While most all our notation is standard
  in some community, readers may not be familiar with all of it. To that end,
  and to ensure completeness of our semantics, we give detailed definitions
  below of the common notation used throughout this document.

  Our formal language is phrased in terms of simple type theory and readers
  familiar with mathematics should not have too much trouble following it
  since mathematics notation already borrows heavily from simple type theory.

  To begin with we will assume that we have a notation of a type of natural
  numbers, <math|\<bbb-N\>>, with <math|0\<of\>\<bbb-N\>>,
  <math|1\<of\>\<bbb-N\>>, and so forth for all other numbers. Given natural
  numbers <math|n\<of\>\<bbb-N\>> and <math|m\<of\>\<bbb-N\>>, we take it for
  granted that we have

  <\itemize>
    <item>notions of arithmetic including <math|n+m>, <math|n*m>, and
    <math|n<rsup|m>>;

    <item>comparison operations including <math|n\<less\>m>,
    <math|n\<leq\>m>, <math|n\<geq\>m>, and <math|n\<gtr\>m>;

    <item>when <math|n\<geq\>m> then the difference <math|n-m> is a natural
    number.
  </itemize>

  We will partake in several notational conveniences. We will generally elide
  parentheses when the value they surround already has has its own brackets.
  For example,

  <\itemize>
    <item>we will write <math|f<around*|\<langle\>|x,y|\<rangle\>>> instead
    of <math|f<around*|(|<around*|\<langle\>|x,y|\<rangle\>>|)>>;

    <item>we will write <math|f<math-tt|[cafe]>> instead of
    <math|f<around*|(|<math-tt|[cafe]>|)>>;

    <item>we will write <math|l<around*|\<lceil\>|n|\<rceil\>>> instead of
    <math|l<around*|[|<around*|\<lceil\>|n|\<rceil\>>|]>>.
  </itemize>

  As you will see, we have a lot of notation with type annotations that are
  used to fully disambiguate them. Often these type annotations can be
  completely inferred from the surrounding context and accordingly we will
  usually omit these annotations to reduce notational clutter and reserve the
  annotated versions for cases where the annotations are ambiguous or where
  we want to draw specific attention to them.

  <section|Algebraic Types>

  We write the primitive unit type as <math|<value|1>>. The unique value of
  the unit type is <math|<around*|\<langle\>||\<rangle\>>\<of\><value|1>>.

  Given types <math|A> and <math|B>, then <math|A+B>, <math|A\<times\>B>, and
  <math|A\<rightarrow\>B> are the sum type (also known as disjoint union
  type), the (Cartesian) product type, and the function type respectively.
  Given <math|a\<of\>A> and <math|b\<of\>B> we denote values of the sum and
  product types as

  <\eqnarray*>
    <tformat|<table|<row|<cell|<injl-long|A|B|<around*|(|a|)>>>|<cell|:>|A+B>|<row|<cell|<injr-long|A|B|<around*|(|b|)>>>|<cell|:>|<cell|A+B>>|<row|<cell|<around*|\<langle\>|a,b|\<rangle\>><rsub|A,B>>|<cell|:>|<cell|A\<times\>B>>>>
  </eqnarray*>

  We will usually omit the annotations, writing
  <math|<injl|<around*|(|a|)>>>, <math|<injr|<around*|(|b|)>>>, and
  <math|<around*|\<langle\>|a,b|\<rangle\>>>.

  We write an expression of type <math|A\<rightarrow\>B> using lambda
  notation:

  <\equation*>
    \<lambda\>x:A\<point\>e\<of\>A\<rightarrow\>B
  </equation*>

  where <math|e> is an expression with <math|x\<of\>A> as a bound variable
  (that may occur or zero or more times in <math|e>). Given
  <math|f\<of\>A\<rightarrow\>B> and <math|a\<of\>A>, then ordinary function
  application retrieves a value of type <math|B>:

  <\equation*>
    f<around*|(|a|)>\<of\>B
  </equation*>

  The type operator <math|\<rightarrow\>> is right associative:

  <\equation*>
    A\<rightarrow\>B\<rightarrow\>C=A\<rightarrow\><around*|(|B\<rightarrow\>C|)>
  </equation*>

  \;

  We define the identity function <math|id<rsub|A>\<of\>A\<rightarrow\>A> as

  <\equation*>
    id<rsub|A>\<assign\>\<lambda\>a:A\<point\>a
  </equation*>

  and given <math|f\<of\>A\<rightarrow\>B> and <math|g\<of\>B\<rightarrow\>C>
  we define their composition <math|g\<circ\>f\<of\>A\<rightarrow\>C> as

  <\equation*>
    g\<circ\>f\<assign\>\<lambda\>a:A\<point\>g<around*|(|f<around*|(|a|)>|)><text|.>
  </equation*>

  \;

  We may also write function definitions in ``application'' style where we
  implicitly define a function in terms of function application. In this
  style we would write the above definitions of the identity function and
  function composition as

  <\eqnarray*>
    <tformat|<table|<row|<cell|id<rsub|A><around*|(|a|)>>|<cell|\<assign\>>|<cell|a>>|<row|<cell|<around*|(|g\<circ\>f|)><around*|(|a|)>>|<cell|\<assign\>>|<cell|g<around*|(|f<around*|(|a|)>|)><text|.>>>>>
  </eqnarray*>

  To access components of sum and product types we define functions using
  pattern matching in application style. For example given <math|a\<of\>A>
  and <math|b\<of\>B>, we define the first and second projection functions as

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<pi\><rsup|A,B><rsub|1><around*|\<langle\>|a,b|\<rangle\>>>|<cell|\<assign\>>|<cell|a>>|<row|<cell|\<pi\><rsup|A,B><rsub|2><around*|\<langle\>|a,b|\<rangle\>>>|<cell|\<assign\>>|<cell|b>>>>
  </eqnarray*>

  and given <math|f\<of\>A\<rightarrow\>C> and
  <math|g\<of\>B\<rightarrow\>C>, we define their copair
  <math|<around*|[|f,g|]>\<of\>A+B\<rightarrow\>C> by the pair of equations

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|[|f,g|]><around*|(|<injl|<around*|(|a|)>>|)>>|<cell|\<assign\>>|<cell|f<around*|(|a|)>>>|<row|<cell|<around*|[|f,g|]><around*|(|<injr|<around*|(|b|)>>|)>>|<cell|\<assign\>>|<cell|g<around*|(|b|)><text|.>>>>>
  </eqnarray*>

  \;

  When we take a product type with itself, we form a square and denote it by
  exponential notation accordingly:

  <\eqnarray*>
    <tformat|<table|<row|<cell|A<rsup|2>>|<cell|\<assign\>>|<cell|A\<times\>A>>>>
  </eqnarray*>

  When we take repeated squares, we denote this by exponential notation with
  successively larger powers of two:

  <\eqnarray*>
    <tformat|<table|<row|<cell|A<rsup|1>>|<cell|\<assign\>>|<cell|A>>|<row|<cell|A<rsup|2>>|<cell|\<assign\>>|<cell|A<rsup|1>\<times\>A<rsup|1>>>|<row|<cell|A<rsup|4>>|<cell|\<assign\>>|<cell|A<rsup|2>\<times\>A<rsup|2>>>|<row|<cell|>|<cell|\<vdots\>>|<cell|>>|<row|<cell|A<rsup|2<rsup|1+n>>>|<cell|\<assign\>>|<cell|A<rsup|2<rsup|n>>\<times\>A<rsup|2<rsup|n>>>>|<row|<cell|>|<cell|\<vdots\>>|<cell|>>>>
  </eqnarray*>

  We define the diagonal function returning a square type,
  <math|\<Delta\><rsub|A>\<of\>A\<rightarrow\>A<rsup|2>>:

  <\equation*>
    \<Delta\><rsub|A><around*|(|a|)>\<assign\><around*|\<langle\>|a,a|\<rangle\>>
  </equation*>

  We define <2> as the Boolean type (or Bit type):

  <\equation*>
    <2>\<assign\><1>+<1>
  </equation*>

  We name the two values of this type, <math|<math-tt|0><rsub|<2>>\<of\><2>>
  and <math|<math-tt|1><rsub|<2>>\<of\><2>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<math-tt|0><rsub|<2>>>|<cell|\<assign\>>|<cell|<injl-long|<value|1>|<value|1>|<around*|\<langle\>||\<rangle\>>>>>|<row|<cell|<math-tt|1><rsub|<2>>>|<cell|\<assign\>>|<cell|<injr-long|<value|1>|<value|1>|<around*|\<langle\>||\<rangle\>>>>>>>
  </eqnarray*>

  <subsection|Records>

  Record types are essentially the same as product types, but with fancy
  syntax. We write a record type enclosed by curly braces.

  <\equation*>
    <around*|{|<tabular|<tformat|<cwith|3|3|1|1|cell-halign|c>|<table|<row|<cell|field<rsub|1>\<of\>A<rsub|1>>>|<row|<cell|field<rsub|2>\<of\>A<rsub|2>>>|<row|<cell|\<vdots\>>>|<row|<cell|field<rsub|n>\<of\>A<rsub|n>>>>>>|}>
  </equation*>

  If <math|R> is the above record type and <math|r\<of\>R>, then we denote
  access the component of the record as follows.

  <\eqnarray*>
    <tformat|<table|<row|<cell|>|<cell|r<around*|[|field<rsub|1>|]>\<of\>A<rsub|1>>|<cell|>>|<row|<cell|>|<cell|r<around*|[|field<rsub|2>|]>\<of\>A<rsub|2>>|<cell|>>|<row|<cell|>|<cell|\<vdots\>>|<cell|>>|<row|<cell|>|<cell|r<around*|[|field<rsub|n>|]>\<of\>A<rsub|n>>|<cell|>>>>
  </eqnarray*>

  To construct a record value given values
  <math|a<rsub|1>\<of\>A<rsub|1>,\<ldots\>,a<rsub|n>\<of\>A<rsub|n>>, we
  again use a curly brace notation.

  <\equation*>
    <around*|{|<tabular|<tformat|<cwith|3|3|1|1|cell-halign|c>|<table|<row|<cell|field<rsub|1>\<assign\>a<rsub|1>>>|<row|<cell|field<rsub|2>\<assign\>a<rsub|2>>>|<row|<cell|\<vdots\>>>|<row|<cell|field<rsub|n>\<assign\>a<rsub|n>>>>>>|}>:<around*|{|<tabular|<tformat|<cwith|3|3|1|1|cell-halign|c>|<table|<row|<cell|field<rsub|1>\<of\>A<rsub|1>>>|<row|<cell|field<rsub|2>\<of\>A<rsub|2>>>|<row|<cell|\<vdots\>>>|<row|<cell|field<rsub|n>\<of\>A<rsub|n>>>>>>|}>
  </equation*>

  <section|Functors>

  A functor <math|\<cal-F\>> is a type parameterized by a free type variable,
  such that whenever <math|A> is a type then <math|\<cal-F\><around*|(|A|)>>
  is a type. Given a function <math|f\<of\>A\<rightarrow\>B>, is it often
  possible to define a new function <math|\<cal-F\>f\<of\>\<cal-F\>A\<rightarrow\>\<cal-F\>B>
  such that for all <math|f\<of\>A\<rightarrow\>B> and
  <math|g\<of\>B\<rightarrow\>C> we have

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<cal-F\>id<rsub|A>>|<cell|=>|<cell|id<rsub|\<cal-F\>A>>>|<row|<cell|\<cal-F\><around*|(|f\<circ\>g|)>>|<cell|=>|<cell|\<cal-F\>f\<circ\>\<cal-F\>g>>>>
  </eqnarray*>

  When this happens we call such a functor a <dfn|covariant functor>. In this
  document all our functors will be covariant functors, and we will simply
  call them <dfn|functor>s.

  <subsection|Option Functor>

  By way of a useful example, we define <maybe> to be the option functor,
  also known as the maybe functor,

  <\eqnarray*>
    <tformat|<table|<row|<cell|<maybe>A>|<cell|\<assign\>>|<cell|<value|1>+A>>|<row|<cell|<maybe>f<around*|(|<injl-long|<value|1>|A|<around*|\<langle\>||\<rangle\>>>|)>>|<cell|\<assign\>>|<cell|<injl-long|<value|1>|B|<around*|\<langle\>||\<rangle\>>>>>|<row|<cell|<maybe>f<around*|(|<injr-long|<value|1>|A|<around*|(|a|)>>|)>>|<cell|\<assign\>>|<cell|<injr-long|<value|1>|B|<around*|(|f<around*|(|a|)>|)>>>>>>
  </eqnarray*>

  where <math|f\<of\>A\<rightarrow\>B>.

  We define special notation for values of ``optional'' types
  <math|<maybe>A>,

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<emptyset\><rsub|A><rsup|<maybe>>>|<cell|\<assign\>>|<cell|<injl-long|<value|1>|A|<around*|\<langle\>||\<rangle\>>>\<of\><maybe>A>>|<row|<cell|\<eta\><rsup|S><rsub|A><around*|(|a|)>>|<cell|\<assign\>>|<cell|<injr-long|<value|1>|A|<around*|(|a|)>>\<of\><maybe>A>>>>
  </eqnarray*>

  where <math|a\<of\>A>.

  This notation is designed to coincide with the monadic notation that we
  will define in Section<nbsp><reference|ss:MonadZero>.

  <subsection|List Functors><label|ss:ListFunctors>

  Given a type <math|A>, we recursively define the list functor
  <math|A<rsup|\<ast\>>> and the non-empty list functor <math|A<rsup|+>>,

  \;

  <\eqnarray*>
    <tformat|<table|<row|<cell|A<rsup|\<ast\>>>|<cell|\<assign\>>|<cell|<maybe>A<rsup|+>>>|<row|<cell|A<rsup|+>>|<cell|\<assign\>>|<cell|A\<times\>A<rsup|\<ast\>>>>|<row|<cell|f<rsup|\<ast\>><around*|(|\<emptyset\><rsup|<maybe>><rsub|A<rsup|+>>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><rsub|B<rsup|+>>>>|<row|<cell|f<rsup|\<ast\>><around*|(|\<eta\><rsup|<maybe>><rsub|A<rsup|+>><around*|(|l|)>|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|<maybe>><rsub|B<rsup|+>><around*|(|f<rsup|+><around*|(|l|)>|)>>>|<row|<cell|f<rsup|+><around*|\<langle\>|a,l|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|f<around*|(|a|)>,f<rsup|\<ast\>><around*|(|l|)>|\<rangle\>>>>>>
  </eqnarray*>

  where <math|f\<of\>A\<rightarrow\>B>.

  We leave implicit the fact that these are inductive types and recursive
  definitions over them need to be checked that they are well-founded.
  Suffice to say that the definitions in this section are all well-defined.

  Given a list <math|l\<of\>A<rsup|\<ast\>>> or a non-empty list
  <math|l\<of\>A<rsup|+>>, we define <math|<around*|\||l|\|>\<of\>\<bbb-N\>>
  to be its length.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\||\<emptyset\><rsup|<maybe>><rsub|A<rsup|+>>|\|>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|<around*|\||\<eta\><rsup|<maybe>><rsub|A<rsup|+>><around*|(|l|)>|\|>>|<cell|\<assign\>>|<cell|<around*|\||l|\|>>>|<row|<cell|<around*|\||<around*|\<langle\>|a,l|\<rangle\>>|\|>>|<cell|\<assign\>>|<cell|1+<around*|\||l|\|>>>>>
  </eqnarray*>

  \;

  To retrieve an element we define lookup functions for lists and non-empty
  lists. Given a natural number <math|n\<of\>\<bbb-N\>> and either list
  <math|l\<of\>A<rsup|\<ast\>>> or a non-empty list <math|l\<of\>A<rsup|+>>,
  in both cases we define <math|l<around*|[|n|]>\<of\><maybe>A> to lookup the
  <math|n>th value in <math|l>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|(|\<emptyset\><rsup|<maybe>><rsub|A<rsup|+>>|)><around*|[|n|]>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><rsub|A>>>|<row|<cell|<around*|(|\<eta\><rsup|<maybe>><rsub|A<rsup|+>><around*|(|l|)>|)><around*|[|n|]>>|<cell|\<assign\>>|<cell|l<around*|[|n|]>>>|<row|<cell|<around*|\<langle\>|a,l|\<rangle\>><around*|[|0|]>>|<cell|\<assign\>>|<cell|\<eta\><rsup|<maybe>><rsub|A><around*|(|a|)>>>|<row|<cell|<around*|\<langle\>|a,l|\<rangle\>><around*|[|1+n|]>>|<cell|\<assign\>>|<cell|l<around*|[|n|]>>>>>
  </eqnarray*>

  Naturally, the lookup returns <math|\<emptyset\>> when the index goes
  beyond the end of the list.

  <\lemma>
    For all <math|n\<of\>\<bbb-N\>> and <math|l\<of\>A<rsup|\<ast\>>> or
    <math|l\<of\>A<rsup|+>>, <math|l<around*|[|n|]>=\<emptyset\>> if and only
    if <math|<around*|\||l|\|>\<leq\>n>.
  </lemma>

  Given a list <math|l\<of\>A<rsup|\<ast\>>> (or a non-empty list
  <math|l\<of\>A<rsup|+>>), we define <math|indexed<around*|(|l|)>\<of\><around*|(|\<bbb-N\>\<times\>A|)><rsup|*\<ast\>>>
  (and <math|indexed<around*|(|l|)>\<of\><around*|(|\<bbb-N\>\<times\>A|)><rsup|*+>>
  respectively) as a list of elements paired with its index,

  <\equation*>
    indexed<around*|(|l|)>\<assign\>indexedRec<around*|(|0,l|)>
  </equation*>

  where

  <\eqnarray*>
    <tformat|<table|<row|<cell|indexedRec<around*|(|i,\<emptyset\><rsup|<maybe>><rsub|A<rsup|+>>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><rsub|<around*|(|\<bbb-N\>\<times\>A|)><rsup|+>>>>|<row|<cell|indexedRec<around*|(|i,\<eta\><rsup|<maybe>><rsub|A<rsup|+>><around*|(|l|)>|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|<maybe>><rsub|<around*|(|\<bbb-N\>\<times\>A|)><rsup|+>><around*|(|indexedRec<around*|(|i,l|)>|)>>>|<row|<cell|indexedRec<around*|(|i,<around*|\<langle\>|a,l|\<rangle\>>|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|<around*|\<langle\>|i,a|\<rangle\>>,indexedRec<around*|(|1+i,l|)>|\<rangle\>><text|.>>>>>
  </eqnarray*>

  <\lemma>
    For all <math|i\<of\>\<bbb-N\>> and <math|l\<of\>A<rsup|\<ast\>>> or
    <math|l\<of\>A<rsup|\<upl\>>>, <math|indexed<around*|(|l|)><around*|[|i|]>=<maybe><around*|(|\<lambda\>a.<around*|\<langle\>|i,a|\<rangle\>>|)><around*|(|l<around*|[|i|]>|)>>.
  </lemma>

  The fold operation on a list is a most general way of consuming a list.
  Given a type <math|A> with a monoid <math|<around*|\<langle\>|\<odot\>,e|\<rangle\>>>
  over that type, we define <math|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|l|)>>
  for both lists <math|l\<of\>A<rsup|\<ast\>>> and non-empty lists
  <math|l\<of\>A<rsup|+>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|\<emptyset\><rsup|<maybe>><rsub|A<rsup|+>>|)>>|<cell|\<assign\>>|<cell|e>>|<row|<cell|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|\<eta\><rsup|<maybe>><rsub|A<rsup|+>><around*|(|l|)>|)>>|<cell|\<assign\>>|<cell|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|l|)>>>|<row|<cell|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|\<langle\>|a,l|\<rangle\>>>|<cell|\<assign\>>|<cell|a\<odot\>fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|l|)>>>>>
  </eqnarray*>

  Often we will write <math|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|l|)>>
  as simply <math|fold<rsup|\<odot\>><around*|(|l|)>> since usually both the
  type and the unit for a monoid is can be inferred from just its binary
  operation.

  For lists, we provide special notations for its two effective constructors
  called <dfn|nil>, <math|\<epsilon\><rsub|A>\<of\>A<rsup|\<ast\>>>, and
  <dfn|cons>, <math|a\<blacktriangleleft\>l\<of\>A<rsup|\<ast\>>>

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<epsilon\><rsub|A>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><rsub|A<rsup|+>>>>|<row|<cell|a\<blacktriangleleft\>l>|<cell|\<assign\>>|<cell|\<eta\><rsup|<maybe>><rsub|A<rsup|+>><around*|\<langle\>|a,l|\<rangle\>>>>>>
  </eqnarray*>

  where <math|a\<of\>A> and <math|l\<of\>A<rsup|\<ast\>>>. As a consequence
  the following equations hold.

  <\eqnarray*>
    <tformat|<table|<row|<cell|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|\<epsilon\><rsub|A>|)>>|<cell|=>|<cell|e>>|<row|<cell|fold<rsup|<around*|\<langle\>|\<odot\>,e|\<rangle\>>><rsub|A><around*|(|a<rsub|0>\<blacktriangleleft\>a<rsub|1>\<blacktriangleleft\>\<ldots\>\<blacktriangleleft\>a<rsub|n>\<blacktriangleleft\>\<epsilon\><rsub|A>|)>>|<cell|=>|<cell|a<rsub|0>\<odot\>a<rsub|1>\<odot\>\<ldots\>\<odot\>a<rsub|n>>>>>
  </eqnarray*>

  For example, given two lists <math|l<rsub|1>,l<rsub|2>\<of\>A<rsup|\<ast\>>>,
  we define the append operation <math|l<rsub|1>\<cdummy\>l<rsub|2>:A<rsup|\<ast\>>>
  using nil and cons

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<epsilon\>\<cdummy\>l>|<cell|\<assign\>>|<cell|l>>|<row|<around*|(|a\<blacktriangleleft\>l<rsub|1>|)>\<cdummy\>l<rsub|2>|<cell|\<assign\>>|<cell|a\<blacktriangleleft\><around*|(|l<rsub|1>\<cdummy\>l<rsub|2>|)>>>>>
  </eqnarray*>

  The append operation together with nil,
  <math|<around*|\<langle\>|\<cdummy\>,\<epsilon\>|\<rangle\>>>, forms a
  monoid over <math|A<rsup|\<ast\>>>. This allows us to define the
  concatenation function <math|\<mu\><rsup|\<ast\>><rsub|A>\<of\>A<rsup|\<ast\>\<ast\>>\<rightarrow\>A<rsup|\<ast\>>>

  <\equation*>
    \<mu\><rsup|\<ast\>><rsub|A><around*|(|l|)>\<assign\>fold<rsub|A<rsup|\<ast\>>><rsup|<around*|\<langle\>|\<cdummy\>,\<epsilon\>|\<rangle\>>><around*|(|l|)>
  </equation*>

  Now it is only natural to define a function that generates a list with one
  element, <math|\<eta\><rsup|\<ast\>><rsub|A>\<of\>A\<rightarrow\>A<rsup|\<ast\>>>.

  <\equation*>
    \<eta\><rsup|\<ast\>><rsub|A><around*|(|a|)>\<assign\>a\<blacktriangleleft\>\<epsilon\>
  </equation*>

  We write replication of a list, <math|l\<of\>A<rsup|\<ast\>>> as
  exponentiation:

  <\eqnarray*>
    <tformat|<table|<row|<cell|l<rsup|0>>|<cell|\<assign\>>|<cell|\<epsilon\>>>|<row|<cell|l<rsup|1+n>>|<cell|\<assign\>>|<cell|l\<cdummy\>l<rsup|n>>>>>
  </eqnarray*>

  We also define quantifier notation for elements of lists. Given a list
  <math|l\<of\>A<rsup|\<ast\>>>, and a predicate <math|P> over <math|A>, we
  define

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<forall\>a\<in\>l\<point\>P<around*|(|a|)>>|<cell|\<assign\>>|<cell|fold<rsup|\<wedge\>><around*|(|P<rsup|\<ast\>><around*|(|l|)>|)>>>|<row|<cell|\<exists\>a\<in\>l\<point\>P<around*|(|a|)>>|<cell|\<assign\>>|<cell|fold<rsup|\<vee\>><around*|(|P<rsup|\<ast\>><around*|(|l|)>|)>>>>>
  </eqnarray*>

  and similarly for a non-empty list <math|l\<of\>A<rsup|+>>:

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<forall\>a\<in\>l\<point\>P<around*|(|a|)>>|<cell|\<assign\>>|<cell|fold<rsup|\<wedge\>><around*|(|P<rsup|+><around*|(|l|)>|)>>>|<row|<cell|\<exists\>a\<in\>l\<point\>P<around*|(|a|)>>|<cell|\<assign\>>|<cell|fold<rsup|\<vee\>><around*|(|P<rsup|+><around*|(|l|)>|)>>>>>
  </eqnarray*>

  <section|Monads>

  A monad, <math|\<cal-M\>>, is a functor that comes with two functions

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<eta\><rsup|\<cal-M\>><rsub|A>>|<cell|:>|<cell|A\<rightarrow\>\<cal-M\>*A>>|<row|<cell|\<mu\><rsup|\<cal-M\>><rsub|A>>|<cell|:>|<cell|\<cal-M\>*\<cal-M\>*A\<rightarrow\>\<cal-M\>*A>>>>
  </eqnarray*>

  that are both natural transformations, meaning for all
  <math|f\<of\>A\<rightarrow\>B>,

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<cal-M\>*f\<circ\>\<eta\><rsup|\<cal-M\>><rsub|A>>|<cell|=>|<cell|\<eta\><rsup|\<cal-M\>><rsub|B>\<circ\>f>>|<row|<cell|\<cal-M\>*f\<circ\>\<mu\><rsup|\<cal-M\>><rsub|A>>|<cell|=>|<cell|\<mu\><rsup|\<cal-M\>><rsub|B>\<circ\>\<cal-M\>*\<cal-M\>*f>>>>
  </eqnarray*>

  The <math|\<eta\><rsup|\<cal-M\>><rsub|A>> and
  <math|\<mu\><rsup|\<cal-M\>><rsub|A>> functions are required to satisfy
  certain coherence laws. These monad laws are best presented using Kleisli
  composition.

  <subsection|Kleisli Morphisms>

  Functions from <math|A> to <math|B> that produce side-effects can often be
  represented by Kleisli morphisms, which are (pure) functions
  <math|A\<rightarrow\>\<cal-M\>*B>, where <math|\<cal-M\>> is a monad that
  captures the particular side-effects of the function in the result. A
  function <math|f\<of\>A\<rightarrow\>\<cal-M\>*B> is called a <dfn|Kleisli
  morphism> from <math|A> to <math|B>. For Kleisli morphisms
  <math|f\<of\>A\<rightarrow\>\<cal-M\>*B> and
  <math|g\<of\>B\<rightarrow\>\<cal-M\>*C> we define the <dfn|Kleisli
  composition> of them as <math|g<above|\<leftarrowtail\>|<very-small|\<cal-M\>>>f\<of\>A\<rightarrow\>\<cal-M\>*C>
  where

  <\equation*>
    g<above|\<leftarrowtail\>|<very-small|\<cal-M\>>>f\<assign\>\<mu\><rsup|\<cal-M\>>\<circ\>\<cal-M\>*g\<circ\>f
  </equation*>

  We will usually omit the annotation.

  The monad laws can be presented in terms of Kleisli composition. For all
  <math|f\<of\>A\<rightarrow\>\<cal-M\>*B>,
  <math|g\<of\>B\<rightarrow\>\<cal-M\>*C>, and
  <math|h\<of\>C\<rightarrow\>\<cal-M\>*D>, we require that Kleisli
  composition satisfy the laws of composition with
  <math|\<eta\><rsup|\<cal-M\>>> as its identity:

  <\eqnarray*>
    <tformat|<table|<row|<cell|f\<leftarrowtail\>\<eta\><rsup|\<cal-M\>><rsub|A>>|<cell|=>|<cell|f>>|<row|<cell|\<eta\><rsup|\<cal-M\>><rsub|B>\<leftarrowtail\>f>|<cell|=>|<cell|f>>|<row|<cell|<around*|(|h\<leftarrowtail\>g|)>\<leftarrowtail\>f>|<cell|=>|<cell|h\<leftarrowtail\><around*|(|g\<leftarrowtail\>f|)>>>>>
  </eqnarray*>

  <subsection|Cartesian Strength>

  In addition to Kleisli composition we define a series of helper functions
  for manipulating products.

  \;

  <center|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|r>|<cwith|1|-1|2|2|cell-hyphen|n>|<cwith|1|-1|2|2|cell-lsep|0>|<cwith|1|-1|1|1|cell-rsep|0>|<table|<row|<cell|<math|\<beta\><rsup|\<cal-M\>><rsub|A,B>>>|<cell|<math|:A\<times\>\<cal-M\>*B\<rightarrow\>\<cal-M\><around*|(|A\<times\>B|)>>>>|<row|<cell|<math|\<beta\><rsup|\<cal-M\>><around*|\<langle\>|a,b|\<rangle\>>>>|<cell|<math|\<assign\>\<cal-M\><around*|(|\<lambda\>x\<point\><around*|\<langle\>|a,x|\<rangle\>>|)><around*|(|b|)>>>>>>>>

  \;

  \;

  <center|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|r>|<cwith|1|-1|2|2|cell-hyphen|n>|<cwith|1|-1|2|2|cell-lsep|0>|<cwith|1|-1|1|1|cell-rsep|0>|<table|<row|<cell|<math|<wide|\<beta\>|\<bar\>><rsup|\<cal-M\>><rsub|A,B>>>|<cell|<math|:\<cal-M\>*A\<times\>B\<rightarrow\>\<cal-M\><around*|(|A\<times\>B|)>>>>|<row|<cell|<math|<wide|\<beta\>|\<bar\>><rsup|\<cal-M\>><around*|\<langle\>|a,b|\<rangle\>>>>|<cell|<math|\<assign\>\<cal-M\><around*|(|\<lambda\>x\<point\><around*|\<langle\>|x,b|\<rangle\>>|)><around*|(|a|)>>>>>>>>

  \;

  \;

  <center|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|r>|<cwith|1|-1|2|2|cell-hyphen|n>|<cwith|1|-1|2|2|cell-lsep|0>|<cwith|1|-1|1|1|cell-rsep|0>|<table|<row|<cell|<math|\<phi\><rsup|\<cal-M\>><rsub|A,B>>>|<cell|<math|:\<cal-M\>*A\<times\>\<cal-M\>*B\<rightarrow\>\<cal-M\><around*|(|A\<times\>B|)>>>>|<row|<cell|<math|\<phi\><rsup|\<cal-M\>>>>|<cell|<math|\<assign\>\<beta\><rsup|\<cal-M\>>\<leftarrowtail\><wide|\<beta\>|\<bar\>><rsup|\<cal-M\>>>>>>>>>

  \;

  \;

  <center|<tabular|<tformat|<cwith|1|-1|1|1|cell-halign|r>|<cwith|1|-1|2|2|cell-hyphen|n>|<cwith|1|-1|2|2|cell-lsep|0>|<cwith|1|-1|1|1|cell-rsep|0>|<table|<row|<cell|<math|<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,B>>>|<cell|<math|:\<cal-M\>*A\<times\>\<cal-M\>*B\<rightarrow\>\<cal-M\><around*|(|A\<times\>B|)>>>>|<row|<cell|<math|<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>>>>|<cell|<math|\<assign\><wide|\<beta\>|\<bar\>><rsup|\<cal-M\>>\<leftarrowtail\>\<beta\><rsup|\<cal-M\>>>>>>>>>

  \;

  The operations <math|\<phi\><rsup|\<cal-M\>><rsub|A,B>> and
  <math|<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,B>> are similar, but
  differ in the order that effects are applied in. Roughly speaking,
  <math|\<phi\><rsup|\<cal-M\>><rsub|A,B>> applies the effects of the first
  component first, while <math|<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,B>>
  applies the effects of the second component first. For some monads, the
  order of the effects is immaterial and <math|\<phi\><rsup|\<cal-M\>><rsub|A,B>=<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,B>>.
  We call such monads <dfn|commutative monads>.

  It is always the case that

  <\equation*>
    \<phi\><rsup|\<cal-M\>><rsub|A,A>\<circ\>\<Delta\><rsub|\<cal-M\>*A>=<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,A>\<circ\>\<Delta\><rsub|\<cal-M\>*A>\<of\>\<cal-M\>*A\<rightarrow\>\<cal-M\><around*|(|A<rsup|2>|)>
  </equation*>

  holds, even for non-commutative monads. In this case, the effect specified
  by the input is duplicated. Compare this with
  <math|\<cal-M\>*\<Delta\><rsub|A>\<of\>\<cal-M\>*A\<rightarrow\>\<cal-M\><around*|(|A<rsup|2>|)>>
  where the contents of type <math|A> are duplicated, but not the effect
  itself. When we have <math|\<cal-M\>*\<Delta\><rsub|A>=\<phi\><rsup|\<cal-M\>><rsub|A,A>\<circ\>\<Delta\><rsub|\<cal-M\>*A>>
  <around*|(|equiv. <math|\<cal-M\>*\<Delta\><rsub|A>=<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,A>\<circ\>\<Delta\><rsub|\<cal-M\>*A>>|)>,
  we say that <math|\<cal-M\>> is an <dfn|idempotent monad>.<\footnote>
    Beware that we are using the definition of idempotent monad from King and
    Wadler<nbsp><cite|King1993>, as opposed to the traditional categorical
    definition of an idempotent monad.
  </footnote> For idempotent monads, the same effect is occurring two or more
  times in a row is equivalent to it occurring once.

  <subsection|Identity Monad>

  The most trivial monad is the identity monad, <math|Id>, where
  <math|Id\<space\>A\<assign\>A> and <math|Id\<space\>f\<assign\>f>. The
  natural transformations <math|\<eta\><rsup|Id><rsub|A>> and
  <math|\<mu\><rsup|Id><rsub|A>> are both the identity function. The identity
  monad captures no side-effects and it is commutative and idempotent.

  <subsection|Monad Zero><label|ss:MonadZero>

  Some monads have a universal <dfn|zero> value

  <\equation*>
    \<emptyset\><rsup|\<cal-M\>><rsub|A>\<of\>\<cal-M\>*A
  </equation*>

  where for all <math|f\<of\>A\<rightarrow\>B>,

  <\equation*>
    \<cal-M\>f<around*|(|\<emptyset\><rsup|\<cal-M\>><rsub|A>|)>=\<emptyset\><rsup|\<cal-M\>><rsub|B>
  </equation*>

  This zero value denotes a side-effect that captures the notion of a failed
  or aborted computation or some kind of empty result.

  The laws for these monads with zero are, again, best expressed using
  Kleisli morphisms. At the risk of some notational confusion, we define
  <math|\<varnothing\><rsup|\<cal-M\>><rsub|A,B>\<of\>A\<rightarrow\>\<cal-M\>*B>
  as a <dfn|zero morphism>.

  <\equation*>
    \<varnothing\><rsup|\<cal-M\>><rsub|A,B><around*|(|a|)>\<assign\>\<emptyset\><rsup|\<cal-M\>><rsub|B>
  </equation*>

  Zero morphisms are required to be an absorbing element for Kleisli
  composition. For all <math|f\<of\>A\<rightarrow\>\<cal-M\>*B> and
  <math|g\<of\>B\<rightarrow\>\<cal-M\>*C> we require that

  <\eqnarray*>
    <tformat|<table|<row|<cell|g<op|\<leftarrowtail\>>\<varnothing\><rsup|\<cal-M\>><rsub|A,B>>|<cell|=>|<cell|\<varnothing\><rsup|\<cal-M\>><rsub|A,C>>>|<row|<cell|\<varnothing\><rsup|\<cal-M\>><rsub|B,C><op|\<leftarrowtail\>>f>|<cell|=>|<cell|\<varnothing\><rsup|\<cal-M\>><rsub|A,C>>>>>
  </eqnarray*>

  (Note: In Haskell, the <verbatim|mzero> value typically is only required to
  satisfy the first equation; however, we require monads with zero to satisfy
  both laws.)

  <subsubsection|Option Monad><label|ss:optionMonad>

  The functor <math|<value|maybe>> forms a monad with the following
  operations:

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<eta\><rsup|<maybe>><rsub|A><around*|(|a|)>>|<cell|\<assign\>>|<cell|<injr|<around*|(|a|)>>>>|<row|<cell|\<mu\><rsup|S><rsub|A><around*|(|<injl|<around*|\<langle\>||\<rangle\>>>|)>>|<cell|\<assign\>>|<cell|<injl|<around*|\<langle\>||\<rangle\>>>>>|<row|<cell|\<mu\><rsup|S><rsub|A><around*|(|<injr|<around*|(|x|)>>|)>>|<cell|\<assign\>>|<cell|x>>>>
  </eqnarray*>

  The option monad is commutative and idempotent. The option monad has a
  zero:

  <\equation*>
    \<emptyset\><rsup|<maybe>><rsub|A>\<assign\><injl|<around*|\<langle\>||\<rangle\>>>
  </equation*>

  There is a natural transformation from the option monad into any monad with
  zero, <math|\<iota\><rsup|\<cal-M\>><rsub|<maybe>,A>\<of\><maybe>A\<rightarrow\>\<cal-M\>*A>:

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<iota\><rsup|\<cal-M\>><rsub|<maybe>,A><around*|(|\<emptyset\><rsup|<maybe>><rsub|A>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|\<cal-M\>><rsub|A>>>|<row|<cell|\<iota\><rsup|\<cal-M\>><rsub|<maybe>,A><around*|(|\<eta\><rsup|<maybe>><rsub|A><around*|(|a|)>|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|\<cal-M\>><rsub|A><around*|(|a|)>>>>>
  </eqnarray*>

  <\lemma>
    For all <math|f:A\<rightarrow\>B>,

    \;

    <\equation*>
      \<iota\><rsup|\<cal-M\>><rsub|<maybe>,B>\<circ\><maybe>f=\<cal-M\>*f\<circ\>\<iota\><rsup|\<cal-M\>><rsub|<maybe>,A>
    </equation*>

    Also

    <\equation*>
      \<iota\><rsup|\<cal-M\>><rsub|<maybe>,A>\<circ\>\<mu\><rsup|<maybe>><rsub|A>=\<mu\><rsup|\<cal-M\>><rsub|A>\<circ\>\<iota\><rsup|\<cal-M\>><rsub|<maybe>,\<cal-M\>*A>\<circ\><maybe>\<iota\><rsup|\<cal-M\>><rsub|<maybe>,A>
      <around*|(|=\<mu\><rsup|\<cal-M\>><rsub|A>\<circ\>\<cal-M\>*\<iota\><rsup|\<cal-M\>><rsub|<maybe>,A>\<circ\>\<iota\><rsup|\<cal-M\>><rsub|<maybe>,<maybe>A>|)>
    </equation*>
  </lemma>

  <section|Multi-bit Words>

  By repeatedly taking products of the bit type we can build the types
  <math|<2><rsup|2<rsup|n>>> which denote <math|2<rsup|n>>-bit words. We
  choose to represent values in big endian format, meaning that given a pair
  representing the low and high bits of a value, the most significant bits
  are stored in the first half. Given a value <math|a\<of\><2><rsup|n>>,
  where <math|n> is a power of two, we recursively define
  <math|<around*|\<lceil\>|a|\<rceil\>><rsub|n>\<of\>\<bbb-N\>> to be the
  number that <math|a> represents:

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<math-tt|0><rsub|<2>>|\<rceil\>><rsub|1>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|<around*|\<lceil\>|<math-tt|1><rsub|<2>>|\<rceil\>><rsub|1>>|<cell|\<assign\>>|<cell|1>>|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|2*n>>|<cell|\<assign\>>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|n>*2<rsup|n>+<around*|\<lceil\>|b|\<rceil\>><rsub|n>>>>>
  </eqnarray*>

  We also make use of the following variation of this value interpretation
  function.

  <\equation*>
    <around*|\<lceil\>|<around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|n,m>\<assign\><around*|\<lceil\>|a|\<rceil\>><rsub|n>*2<rsup|m>+<around*|\<lceil\>|b|\<rceil\>><rsub|m>
  </equation*>

  These value interpretation functions are all injective (one-to-one) and we
  can choose a left inverse. Given <math|m\<of\>\<bbb-N\>>, we implicitly
  define <math|<around*|\<lfloor\>|m|\<rfloor\>><rsub|n>\<of\><2><rsup|n>>
  such that <math|<around*|\<lceil\>|<around*|\<lfloor\>|m|\<rfloor\>><rsub|n>|\<rceil\>><rsub|n>\<equiv\>m
  <around*|(|mod 2<rsup|n>|)>>. We have chosen
  <math|<around*|\<lfloor\>|m|\<rfloor\>><rsub|n>> so that it represents
  <math|m> modulo <math|2<rsup|n>>.

  We can equip the type <math|<2><rsup|n>> with addition and multiplication
  operations, so that <math|<around*|\<lfloor\>|\<cdummy\>|\<rfloor\>><rsub|n>>
  becomes a semiring homomorphism. Given <math|a\<of\><2><rsup|n>> and
  <math|b\<of\><2><rsup|n>>, we define <math|a<around*|\<lfloor\>|+|\<rfloor\>><rsub|n>b\<of\><2><rsup|n>>
  and <math|a*<around*|\<lfloor\>|\<times\>|\<rfloor\>><rsub|n>b\<of\><2><rsup|n>>
  such that

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lfloor\>|m<rsub|1>|\<rfloor\>><rsub|n><around*|\<lfloor\>|+|\<rfloor\>><rsub|n><around*|\<lfloor\>|m<rsub|2>|\<rfloor\>><rsub|n>>|<cell|=>|<cell|<around*|\<lfloor\>|m<rsub|1>+m<rsub|2>|\<rfloor\>><rsub|n>>>|<row|<cell|<around*|\<lfloor\>|m<rsub|1>|\<rfloor\>><rsub|n><around*|\<lfloor\>|\<times\>|\<rfloor\>><rsub|n><around*|\<lfloor\>|m<rsub|2>|\<rfloor\>><rsub|n>>|<cell|=>|<cell|<around*|\<lfloor\>|m<rsub|1>*m<rsub|2>|\<rfloor\>><rsub|n>>>>>
  </eqnarray*>

  \;

  We write <math|<math-tt|0><rsub|<2><rsup|4>>,<math-tt|1><rsub|<2><rsup|4>>,\<ldots\>,<math-tt|f><rsub|<2><rsup|4>>>
  to denote the 16 values of <math|<2><rsup|4>> that represent their
  respective hexadecimal values. Similarly, we write
  <math|<math-tt|00><rsub|<2><rsup|8>>,<math-tt|01><rsub|<2><rsup|8>>,\<ldots\>,<math-tt|ff><rsub|<2><rsup|8>>>
  to denote the 256 values of <math|<2><rsup|8>>, and so forth. It is worth
  observing that for hexadecimal digits <math|<math-tt|<var|x>>> and
  <math|<math-tt|<var|y>>>, we have <math|<math-tt|<var|xy>><rsub|<2><rsup|8>>=<around*|\<langle\>|<math-tt|<var|x>><rsub|<2><rsup|4>>,<math-tt|<var|y>><rsub|<2><rsup|4>>|\<rangle\>>>.

  <subsection|Byte Strings>

  The type <math|<around*|(|<2><rsup|8>|)><rsup|\<ast\>>> is known as byte
  strings. We will write byte string values as sequences of hexadecimal
  digits surrounded by square brackets, e.g.
  <math|<math-tt|[cafe]><rsub|<2><rsup|8>>> denotes
  <math|<math-tt|ca><rsub|<2><rsup|8>>\<blacktriangleleft\><math-tt|fe><rsub|<2><rsup|8>>\<blacktriangleleft\>\<epsilon\><rsub|<2><rsup|8>>>
  (whereas <math|<math-tt|cafe><rsub|<2><rsup|16>>> denotes
  <math|<around*|\<langle\>|<math-tt|ca><rsub|<2><rsup|8>>,<math-tt|fe><rsub|<2><rsup|8>>|\<rangle\>>>).
  For all these values, we may omit the subscript when the interpretation is
  clear from the context.

  Words larger than a byte are commonly encoded as byte strings in either big
  endian or little endian order. We define
  <math|BE<rsub|n>\<of\><2><rsup|n>\<rightarrow\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>>
  and <math|LE<rsub|n>\<of\><2><rsup|n>\<rightarrow\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>>
  as big endian and little endian encodings of words respectively for
  <math|n\<geq\>8>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|LE<rsub|8><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|\<ast\>><around*|(|a|)>>>|<row|<cell|LE<rsub|2*n><around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>>|<cell|\<assign\>>|<cell|LE<rsub|n><around*|(|a<rsub|2>|)>\<cdummy\>LE<rsub|n><around*|(|a<rsub|1>|)><text|<htab|5mm>(when
    <math|8\<leq\>n>)>>>|<row|<cell|BE<rsub|8><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|\<ast\>><around*|(|a|)>>>|<row|<cell|BE<rsub|2*n><around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>>|<cell|\<assign\>>|<cell|BE<rsub|n><around*|(|a<rsub|1>|)>\<cdummy\>BE<rsub|n><around*|(|a<rsub|2>|)><text|<htab|5mm>(when
    <math|8\<leq\>n>)>>>>>
  </eqnarray*>

  <subsection|Bit Strings>

  The type <math|<2><rsup|\<ast\>>> is known as bit strings. We will write
  bit string values as sequences of binary digits surrounded by square
  brackets, e.g. <math|<math-tt|[0110]><rsub|<2>>> denotes
  <math|<math-tt|0><rsub|<2>>\<blacktriangleleft\><math-tt|1><rsub|<2>>\<blacktriangleleft\><math-tt|1><rsub|<2>>\<blacktriangleleft\><math-tt|0><rsub|<2>>\<blacktriangleleft\>\<epsilon\><rsub|<2>>>.
  Again, we may omit the subscript when the interpretation is clear from
  context.

  <chapter|Core Simplicity>

  Simplicity is a typed functional programming language based on Gentzen's
  sequent calculus<nbsp><cite|gentzen>. The core language consists of nine
  combinators for forming expressions. These nine combinators capture the
  computational power of Simplicity. In later chapters other combinators will
  extend this core language and provide other effects to handle input and
  access the transaction that provides context for the Simplicity program.

  <section|Types>

  This section introduces the abstract syntax and semantics types available
  in Simplicity. Simplicity uses a particular subset of the simple type
  theory we developed in Chapter<nbsp><reference|chapter:preliminaries>.

  <subsection|Abstract Syntax>

  Simplicity has only three kinds of types:

  <\itemize-minus>
    <item>The unit type, <value|1>.

    <item>The sum of two Simplicity types, <math|A+B>.

    <item>The product of two Simplicity types, <math|A\<times\>B>.
  </itemize-minus>

  \;

  Simplicity has neither function types nor recursive types. Every type in
  Simplicity can only contain a finite number of values. For example, the
  type <2>, which is <math|<value|1>+<value|1>>, has exactly two values,
  namely <injl-long|<value|1>|<value|1>|<around*|\<langle\>||\<rangle\>>> and
  <injr-long|<value|1>|<value|1>|<around*|\<langle\>||\<rangle\>>>. The type
  <math|<around*|(|<value|1>+<value|1>|)>\<times\><around*|(|<value|1>+<value|1>|)>>
  has exactly four values. As you can see, the number of values that a type
  contains can be easily calculated by interpreting the type as an arithmetic
  expression. Be aware that types are not arithmetic expressions. For
  example, the types <math|<around*|(|<value|1>+<value|1>|)>+<around*|(|<value|1>+<value|1>|)>>
  and <math|<around*|(|<value|1>+<value|1>|)>\<times\><around*|(|<value|1>+<value|1>|)>>
  are distinct and not interchangeable.

  <subsection|Formal Syntax>

  Formally we define the abstract syntax of types as an inductive type in
  Coq:

  <\render-code>
    <\verbatim>
      <strong|Inductive> Ty : Set :=

      \| Unit : Ty

      \| Sum \ : Ty -\<gtr\> Ty -\<gtr\> Ty

      \| Prod : Ty -\<gtr\> Ty -\<gtr\> Ty.
    </verbatim>
  </render-code>

  <subsection|Formal Semantics>

  Formally we define the denotational semantics of Simplicity types as a
  function from syntax to Coq types:

  \;

  <\verbatim>
    Fixpoint tySem (X : Ty) : Set :=

    match X with

    \| Unit =\<gtr\> Datatypes.unit

    \| Sum A B =\<gtr\> tySem A + tySem B

    \| Prod A B =\<gtr\> tySem A * tySem B

    end.
  </verbatim>

  <section|Terms>

  Simplicity programs are composed of terms that denote functions between
  types. Every Simplicity term is associated with an input type and an output
  type and we write a type annotated term as <math|t\<of\>A\<vdash\>B> where
  <math|t> is the term, <math|A> is the input type and <math|B> is the output
  type. We write <math|<around*|\<llbracket\>|t|\<rrbracket\>>\<of\>A\<rightarrow\>B>
  for the function that the term <math|t> denotes.

  Core Simplicity has nine combinators for forming well-typed terms.

  <subsection|Identity>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|iden><rsub|A>\<of\>A\<vdash\>A>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<samp|iden><rsub|A>|\<rrbracket\>>\<assign\>\<lambda\>a\<point\>a
  </equation*>

  For every Simplicity type <math|A>, we have an identity term that denotes
  the identity function for that type.

  We can also write the semantics in application style as

  <\equation*>
    <around*|\<llbracket\>|<samp|iden><rsub|A>|\<rrbracket\>><around*|(|a|)>\<assign\>a
  </equation*>

  which is just a different way of writing the same definition. However,
  please note that the <math|a> argument is an argument of the function
  denoted by <math|<samp|iden><rsub|A>> and is not an argument to the
  Simplicity term itself.

  <subsection|Composition>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s\<of\>A\<vdash\>B>>|<cell|<math|t\<of\>B\<vdash\>C>>>>>>>>|<row|<cell|<math|<math-ss|comp><rsub|A,B,C>
    s t\<of\>A\<vdash\>C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math-ss|comp><rsub|A,B,C> s
    t|\<rrbracket\>>\<assign\><around*|\<llbracket\>|t|\<rrbracket\>>\<circ\><around*|\<llbracket\>|s|\<rrbracket\>>
  </equation*>

  The composition combinator functionally composes its two arguments,
  <math|s> and <math|t>, when the output type of <math|s> matches the input
  type of <math|t>.

  <subsection|Constant Unit>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<math-ss|unit><rsub|A>\<of\>A\<vdash\><value|1>>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math-ss|unit><rsub|A>|\<rrbracket\>>\<assign\>\<lambda\>a\<point\><around*|\<langle\>||\<rangle\>>
  </equation*>

  The unit term denotes the constant function that always returns
  <math|<around*|\<langle\>||\<rangle\>>>, the unique value of the unit type.
  The function's argument is ignored and we have a constant unit term for
  every type of input.

  We can also write semantics in application style as

  <\equation*>
    <around*|\<llbracket\>|<samp|unit><rsub|A>|\<rrbracket\>><around*|(|a|)>\<assign\><around*|\<langle\>||\<rangle\>><text|.>
  </equation*>

  We will use application style when writing the definition of the remaining
  combinators, trusting that the reader will be mindful of the distinction
  between arguments of the combinators versus the argument of the function
  that the Simplicity term denotes.

  <subsection|Left Injection>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|t\<of\>A\<vdash\>B>>>|<row|<cell|<math|<math-ss|injl><rsub|A,B,C>
    t\<of\>A\<vdash\>B+C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math-ss|injl><rsub|A,B,C>
    t|\<rrbracket\>><around*|(|a|)>\<assign\><injl|<around*|(|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|)>>
  </equation*>

  The left injection combinator composes a left-tag with its argument
  <math|t>.

  <subsection|Right Injection>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|t\<of\>A\<vdash\>C>>>|<row|<cell|<math|<math-ss|injr><rsub|A,B,C>
    t\<of\>A\<vdash\>B+C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math-ss|injr><rsub|A,B,C>
    t|\<rrbracket\>><around*|(|a|)>\<assign\><injr|<around*|(|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|)>>
  </equation*>

  The right injection combinator composes a right-tag with its argument
  <math|t>.

  <subsection|Case>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s\<of\>A\<times\>C\<vdash\>D>>|<cell|<math|t\<of\>B\<times\>C\<vdash\>D>>>>>>>>|<row|<cell|<math|<math-ss|case><rsub|A,B,C,D>
    s t\<of\><around*|(|A+B|)>\<times\>C\<vdash\>D>>>>>>
  </with>

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|case><rsub|A,B,C,D>
    s t|\<rrbracket\>><around*|\<langle\>|<injl|<around*|(|a|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|s|\<rrbracket\>><around*|\<langle\>|a,c|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|case><rsub|A,B,C,D>
    s t|\<rrbracket\>><around*|\<langle\>|<injr|<around*|(|b|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><around*|\<langle\>|b,c|\<rangle\>>>>>>
  </eqnarray*>

  The case combinator is Simplicity's only branching operation. Given a pair
  of values with the first component being a sum type, this combinator
  evaluates either its <math|s> or <math|t> argument, depending on which tag
  the first component has, on the pair of inputs.

  <subsection|Pair>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s\<of\>A\<vdash\>B>>|<cell|<math|t\<of\>A\<vdash\>C>>>>>>>>|<row|<cell|<math|<math-ss|pair><rsub|A,B,C>
    s t\<of\>A\<vdash\>B\<times\>C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math-ss|pair><rsub|A,B,C> s
    t|\<rrbracket\>><around*|(|a|)>\<assign\><around*|\<langle\>|<around*|\<llbracket\>|s|\<rrbracket\>><around*|(|a|)>,<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|\<rangle\>>
  </equation*>

  The pair combinator evaluates both its arguments, <math|s> and <math|t>, on
  the same input and returns the pair of the two results.

  <subsection|Take>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|t\<of\>A\<vdash\>C>>>|<row|<cell|<math|<math-ss|take><rsub|A,B,C>
    t\<of\>A\<times\>B\<vdash\>C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math-ss|take><rsub|A,B,C>
    t|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>\<assign\><around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>
  </equation*>

  The take combinator denotes a function on pairs that passes its first
  component to <math|t> and ignores its second component.

  <subsection|Drop>

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|t\<of\>B\<vdash\>C>>>|<row|<cell|<math|<math-ss|drop><rsub|A,B,C>
    t\<of\>A\<times\>B\<vdash\>C>>>>>>
  </with>

  <\equation*>
    <around*|\<llbracket\>|<math-ss|drop><rsub|A,B,C>
    t|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>\<assign\><around*|\<llbracket\>|t|\<rrbracket\>><around*|(|b|)>
  </equation*>

  The drop combinator denotes a function on pairs that passes its second
  component to <math|t> and ignores its first component.

  <subsection|Formal Syntax>

  We define the formal syntax of well-typed core Simplicity terms as an
  inductive family in Coq:

  <\render-code>
    <\verbatim>
      <strong|Inductive> Term : Ty -\<gtr\> Ty -\<gtr\> Set :=

      \| iden : forall {A}, Term A A

      \| comp : forall {A B C}, Term A B -\<gtr\> Term B C -\<gtr\> Term A C

      \| unit : forall {A}, Term A Unit

      \| injl : forall {A B C}, Term A B -\<gtr\> Term A (Sum B C)

      \| injr : forall {A B C}, Term A C -\<gtr\> Term A (Sum B C)

      \| case : forall {A B C D},

      \ \ \ \ Term (Prod A C) D -\<gtr\> Term (Prod B C) D -\<gtr\> Term
      (Prod (Sum A B) C) D

      \| pair : forall {A B C}, Term A B -\<gtr\> Term A C -\<gtr\> Term A
      (Prod B C)

      \| take : forall {A B C}, Term A C -\<gtr\> Term (Prod A B) C

      \| drop : forall {A B C}, Term B C -\<gtr\> Term (Prod A B) C.
    </verbatim>
  </render-code>

  <subsection|Formal Semantics>

  The formal semantics for core Simplicity in Coq recursively interprets each
  term as a function between the formal semantics of its associated types:

  \;

  <\verbatim>
    Fixpoint eval {A B} (x : Term A B) : tySem A -\<gtr\> tySem B :=

    match x in Term A B return tySem A -\<gtr\> tySem B with

    \| iden =\<gtr\> fun a =\<gtr\> a

    \| comp s t =\<gtr\> fun a =\<gtr\> eval t (eval s a)

    \| unit =\<gtr\> fun _ =\<gtr\> tt

    \| injl t =\<gtr\> fun a =\<gtr\> inl (eval t a)

    \| injr t =\<gtr\> fun a =\<gtr\> inr (eval t a)

    \| case s t =\<gtr\> fun p =\<gtr\> let (ab, c) := p in

    \ \ \ \ match ab with

    \ \ \ \ \| inl a =\<gtr\> eval s (a, c)

    \ \ \ \ \| inr b =\<gtr\> eval t (b, c)

    \ \ \ \ end

    \| pair s t =\<gtr\> fun a =\<gtr\> (eval s a, eval t a)

    \| take t =\<gtr\> fun ab =\<gtr\> eval t (fst ab)

    \| drop t =\<gtr\> fun ab =\<gtr\> eval t (snd ab)

    end.
  </verbatim>

  <section|Example Simplicity>

  Simplicity is not meant to be a language to directly write programs in. It
  is intended to be a backend language that some other language (or
  languages) is complied or translated to. However, one can program directly
  in Simplicity just as one can write programs directly in an assembly
  language.

  Because the core Simplicity language may seem meager, it is worthwhile to
  see how one can build up sophisticated functions in it.

  <subsection|Bit Operations><label|ss:bitOps>

  For the bit type, <2>, we can define core Simplicity terms that represent
  the two constant functions that return this type:

  <\eqnarray*>
    <tformat|<table|<row|<cell|<math-ss|false><rsub|A>>|<cell|\<assign\>>|<cell|<math-ss|injl><rsub|A,<value|1>,<value|1>>
    <math-ss|unit>\<of\>A\<vdash\><2>>>|<row|<cell|<math-ss|true><rsub|A>>|<cell|\<assign\>>|<cell|<math-ss|injr><rsub|A,<value|1>,<value|1>>
    <math-ss|unit>\<of\>A\<vdash\><2>>>>>
  </eqnarray*>

  From these definitions, we can prove that <math|<math-ss|false>> and
  <math|<math-ss|true>> have the following semantics.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|false>|\<rrbracket\>><around*|(|a|)>>|<cell|=>|<cell|<math-tt|0><rsub|<2>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|true>|\<rrbracket\>><around*|(|a|)>>|<cell|=>|<cell|<math-tt|1><rsub|<2>>>>>>
  </eqnarray*>

  Next, we define a condition combinator to branch based on the value of a
  bit using <math|<math-ss|case>> and <samp|drop>. The first argument is the
  ``then'' clause and the second argument is the ``else'' clause.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s\<of\>A\<vdash\>B>>|<cell|<math|t\<of\>A\<vdash\>B>>>>>>>>|<row|<cell|<math|<math-ss|cond><rsub|A,B>
    s t\<assign\><math-ss|case><rsub|<value|1>,<value|1>,A,B>
    <around*|(|<math-ss|drop> t|)> <around*|(|<math-ss|drop>
    s|)>\<of\><2>\<times\>A\<vdash\>B>>>>>>
  </with>

  \;

  We can prove that <math|<math-ss|cond>> has the following semantics.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|cond> s
    t|\<rrbracket\>><around*|\<langle\>|<math-tt|1><rsub|<2>>,a|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|s|\<rrbracket\>><around*|(|a|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|cond>
    s t|\<rrbracket\>><around*|\<langle\>|<math-tt|0><rsub|<2>>,a|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>>>>>
  </eqnarray*>

  With these fundamental operations for bits in hand, we can define standard
  Boolean connectives:

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|t\<of\>A\<vdash\><2>>>>>>>>>|<row|<cell|<math|<math-ss|not><rsub|A>
    t\<assign\><math-ss|comp><rsub|A,<2>\<times\><value|1>,<2>>
    <around*|(|<math-ss|pair> t <math-ss|unit>|)> <around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>\<of\>A\<vdash\><2>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s\<of\>A\<vdash\><2>>>|<cell|<math|t\<of\>A\<vdash\><2>>>>>>>>>|<row|<cell|<math|<math-ss|and><rsub|A>
    s t\<assign\><math-ss|comp><rsub|A,<2>\<times\>A,<2>>
    <around*|(|<math-ss|pair> s <math-ss|iden>|)> <around*|(|<math-ss|cond> t
    <math-ss|false>|)>\<of\>A\<vdash\><2>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s\<of\>A\<vdash\><2>>>|<cell|<math|t:A\<vdash\><2>>>>>>>>>|<row|<cell|<math|<math-ss|or><rsub|A>
    s t\<assign\><math-ss|comp><rsub|A,<2>\<times\>A,<2>>
    <around*|(|<math-ss|pair> s <math-ss|iden>|)> <around*|(|<math-ss|cond>
    <math-ss|true> t|)>\<of\>A\<vdash\><2>>>>>>>
  </with>

  \;

  We use combinators to define <samp|and> and <samp|or> in order to give them
  short-circuit evaluation behaviour. Short-circuit evaluation useful because
  if we know the second branch does not need to be evaluated, the source code
  for it can be pruned at redemption time (see
  Section<nbsp><reference|ss:pruning>). If instead we directly defined the
  Boolean functions with types <math|<math-ss|and-func>:<2>\<times\><2>\<vdash\><2>>
  and <math|<math-ss|or-func>:<2>\<times\><2>\<vdash\><2>>, then the two
  arguments to <samp|and-func> and <samp|or-func> would both be fully
  evaluated under strict semantics (see Section<nbsp><reference|ss:monadicSemantics>).
  For the <samp|not> combinator, this is less of an issue, but we define it
  in combinator form to be consistent.

  <subsection|Simplicity Notation>

  In the previous section, we were relatively detailed with the annotations
  given to the definitions. Going forward we will be a bit more lax in the
  presentation. We will also begin using some notation to abbreviate terms.

  <\eqnarray*>
    <tformat|<table|<row|<cell|s \<vartriangle\>
    t>|<cell|\<assign\>>|<cell|<math-ss|pair> s
    t>>|<row|<cell|s;t>|<cell|\<assign\>>|<cell|<math-ss|comp> s t>>>>
  </eqnarray*>

  with the <math|\<vartriangle\>> operator having higher precedence than the
  ; operator.

  Composition of sequences of <samp|drop> and <samp|take> with <samp|iden> is
  a very common way of picking data from a nested tuple input. To make this
  more concise we will use the following notation.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<math-ss|H>>|<cell|\<assign\>>|<cell|<math-ss|iden>>>|<row|<cell|<math-ss|O>s<math-ss|>>|<cell|\<assign\>>|<cell|<math-ss|take>
    s>>|<row|<cell|<math-ss|I>s<math-ss|>>|<cell|\<assign\>>|<cell|<math-ss|drop>
    s>>>>
  </eqnarray*>

  where <math|s> is a string of <samp|I>'s and <samp|O>'s that ends with
  <samp|H>.

  <subsection|Generic Equality>

  With our notion of a bit in hand, we can build Simplicity predicates of
  type <math|A\<vdash\><2>>. For example, for any Simplicity type <math|A> we
  can build a Simplicity predicate <math|<math-ss|eq><rsub|A>\<of\>A\<times\>A\<vdash\><2>>,
  that decides if two values of the same type are equal or not.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<math-ss|eq><rsub|<1>>>|<cell|\<assign\>>|<cell|<math-ss|true>>>|<row|<cell|<math-ss|eq><rsub|A+B>>|<cell|\<assign\>>|<cell|<math-ss|case>
    <around*|(|<math-ss|IH> \<vartriangle\> <math-ss|OH>;<math-ss|case>
    <math-ss|eq><rsub|A> <math-ss|false>|)> <around*|(|<math-ss|IH>
    \<vartriangle\> <math-ss|OH>;<math-ss|case> <math-ss|false>
    <math-ss|eq><rsub|B>|)>>>|<row|<cell|<math-ss|eq><rsub|A*\<times\>B>>|<cell|\<assign\>>|<cell|<around*|(|<math-ss|OOH>
    \<vartriangle\> <math-ss|IOH>;<math-ss|eq><rsub|A>|)> \<vartriangle\>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IIH>|)>; <math-ss|cond>
    <math-ss|eq><rsub|B> <math-ss|false>>>>>
  </eqnarray*>

  <\theorem>
    Given any Simplicity type A, for values
    <math|a<rsub|0>,a<rsub|1>\<of\>A>,

    <\equation*>
      <around*|\<llbracket\>|<math-ss|eq><rsub|A>|\<rrbracket\>><around*|\<langle\>|a<rsub|0>,a<rsub|1>|\<rangle\>>=<math-tt|1><rsub|<2>><text|
      if and only if >a<rsub|0>=a<rsub|1>.
    </equation*>
  </theorem>

  <subsection|Arithmetic>

  Using techniques familiar from digital logic, we can build an adders and
  full adders from our Boolean operations defined in
  Section<nbsp><reference|ss:bitOps>. We begin with definitions of the single
  bit full adder.

  \;

  <\render-code>
    <math|<math-ss|full-add><rsub|1>\<of\><2>\<times\><around*|(|<2>\<times\><2>|)>\<vdash\><2><rsup|2>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-add><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|maj><rsub|1>
    \<vartriangle\> <math|<math-ss|xor3><rsub|1>>>>>>>>>>>>>
  </render-code>

  where

  <\render-code>
    <math|<math-ss|maj><rsub|1>\<of\><2>\<times\><around*|(|<2>\<times\><2>|)>\<vdash\><2>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|maj><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|cond>
    <around*|(|<math-ss|cond> <math-ss|true> <math-ss|iden>|)>
    <around*|(|<math-ss|cond> <math-ss|iden> <math-ss|false>|)>>>>>>>>>>>>
  </render-code>

  and

  <\render-code>
    <math|<math-ss|xor3><rsub|1>\<of\><2>\<times\><around*|(|<2>\<times\><2>|)>\<vdash\><2>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|xor3><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|cond>
    <around*|(|<math-ss|cond> <math-ss|iden> <around*|(|<math-ss|not>
    <math-ss|iden>|)>|)> <around*|(|<math-ss|cond> <around*|(|<math-ss|not>
    <math-ss|iden>|)> <math-ss|iden>|)>>>>>>>>>>>>
  </render-code>

  The full adder meets the following specification.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-add><rsub|1>|\<rrbracket\>><around*|\<langle\>|c,<around*|\<langle\>|a,b|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|1>+<around*|\<lceil\>|b|\<rceil\>><rsub|1>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>>>>
  </eqnarray*>

  It is easy to exhaustively check the above equations because there are only
  eight inputs to consider. We will illustrate this for a single case where
  <math|a=<math-tt|1><rsub|<2>>>, <math|b=<math-tt|0><rsub|<2>>>, and
  <math|c=<math-tt|1><rsub|<2>>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-add><rsub|1>|\<rrbracket\>><around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2>>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|maj><rsub|1>
    \<vartriangle\> <math|<math-ss|xor3><rsub|1>>|\<rrbracket\>><around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<around*|\<llbracket\>|<math-ss|<math|<math-ss|maj><rsub|1>>>|\<rrbracket\>><around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>|\<rangle\>>,<around*|\<llbracket\>|<math|<math-ss|xor3><rsub|1>>|\<rrbracket\>><math|<around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>|\<rangle\>>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<around*|\<llbracket\>|<math|<math-ss|cond>
    <around*|(|<math-ss|cond> <math-ss|true> <math-ss|iden>|)>
    <around*|(|<math-ss|cond> <math-ss|iden>
    <math-ss|false>|)>>|\<rrbracket\>><around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>|\<rangle\>>,<around*|\<llbracket\>|<math|<math-ss|xor3><rsub|1>>|\<rrbracket\>><math|<around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>|\<rangle\>>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<around*|\<llbracket\>|<math|<math|<math-ss|cond>
    <math-ss|true> <math-ss|iden>>>|\<rrbracket\>><around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>,<around*|\<llbracket\>|<math|<math-ss|xor3><rsub|1>>|\<rrbracket\>><math|<around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>|\<rangle\>>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<around*|\<llbracket\>|<math|<math|<math-ss|true>>>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>,<around*|\<llbracket\>|<math|<math-ss|xor3><rsub|1>>|\<rrbracket\>><math|<around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>|\<rangle\>>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<llbracket\>|<math|<math-ss|xor3><rsub|1>>|\<rrbracket\>><math|<around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>|\<rangle\>>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<llbracket\>|<math|<math|<math-ss|cond>
    <around*|(|<math-ss|cond> <math-ss|iden> <around*|(|<math-ss|not>
    <math-ss|iden>|)>|)> <around*|(|<math-ss|cond> <around*|(|<math-ss|not>
    <math-ss|iden>|)> <math-ss|iden>|)>>>|\<rrbracket\>><math|<around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>|\<rangle\>>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<llbracket\>|<math|<math|<math-ss|cond>
    <math-ss|iden> <around*|(|<math-ss|not>
    <math-ss|iden>|)>>>|\<rrbracket\>><math|<around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|1><rsub|<2>>,<around*|\<llbracket\>|<math|<math|<math-ss|iden>>>|\<rrbracket\>><math|<around*|(|<math-tt|0><rsub|<2>>|)>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|1><rsub|<2>>,<math|<math-tt|0><rsub|<2>>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<math-tt|1><rsub|<2>>|\<rceil\>><rsub|1>\<cdot\>2<rsup|1>+<around*|\<lceil\>|<math-tt|0><rsub|<2>>|\<rceil\>><rsub|1>>>|<row|<cell|>|<cell|=>|<cell|1\<cdot\>2+0>>|<row|<cell|>|<cell|=>|<cell|2>>|<row|<cell|>|<cell|=>|<cell|1+0+1>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<math-tt|1><rsub|<2>>|\<rceil\>><rsub|1>+<around*|\<lceil\>|<math-tt|0><rsub|<2>>|\<rceil\>><rsub|1>+<around*|\<lceil\>|<math-tt|1><rsub|<2>>|\<rceil\>><rsub|1>>>>>
  </eqnarray*>

  The calculations for the other cases are similar.

  Next, we recursively build full adders for any word size.

  <\render-code>
    <math|<math-ss|full-add><rsub|2*n>\<of\><2>\<times\><around*|(|<2><rsup|2*n>\<times\><2><rsup|2*n>|)>\<vdash\><2>\<times\><2><rsup|2*n>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-add><rsub|2*n>>>|<cell|:=>|<cell|<math|<math-ss|drop>
    <around*|(|<math-ss|OOH> \<vartriangle\> <math-ss|IOH>|)> \<vartriangle\>
    <around*|(|<math-ss|OH>\<vartriangle\> <math-ss|drop>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IIH>|)>
    ;<math-ss|full-add><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IIH>
    \<vartriangle\> <around*|(|<math-ss|IOH>\<vartriangle\> <math-ss|OH>
    ;<math-ss|full-add><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IOH>
    \<vartriangle\> <around*|(|<math-ss|IIH> \<vartriangle\>
    <math-ss|OH>|)>>>>>>>>>>>>
  </render-code>

  We generalize the specification of the single bit full adder to the
  multi-bit full adders.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-add><rsub|n>|\<rrbracket\>><around*|\<langle\>|c,<around*|\<langle\>|a,b|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|1,n>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|n>+<around*|\<lceil\>|b|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>>>>
  </eqnarray*>

  <\theorem>
    For all <math|n> which is a power of 2, and for all <math|a:<2><rsup|n>>,
    <math|b:<2><rsup|n>>, and <math|c:<2>>, we have that
    <math|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-add><rsub|n>|\<rrbracket\>><around*|\<langle\>|c,<around*|\<langle\>|a,b|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|1,n>=<around*|\<lceil\>|a|\<rceil\>><rsub|n>+<around*|\<lceil\>|b|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>.
  </theorem>

  <\proof>
    We prove <math|<math-ss|full-add><rsub|n>> meets its specification by
    induction on <math|n>. As mentioned before, the
    <math|<math-ss|full-add><rsub|1>> case is easily checked by verifying all
    eight possible inputs. Next, we prove that
    <math|<math-ss|full-add><rsub|2*n>> meets its specification under the
    assumption that <math|<math-ss|full-add><rsub|n>> does. Specifically we
    need to show that

    <\equation>
      <around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-add><rsub|2*n>|\<rrbracket\>><around*|\<langle\>|c,<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>,<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|1,2*n>=<around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1><label|full-adder-spec>
    </equation>

    Let us first consider the right hand side of equation
    <reference|full-adder-spec>. By the definition of our value function we
    have that

    <\eqnarray*>
      <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>|<cell|=>|<cell|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|a<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|b<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|a<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>>>>
    </eqnarray*>

    By our inductive hypothesis, we have that

    <\equation*>
      <around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-add><rsub|n>|\<rrbracket\>><around*|\<langle\>|c,<around*|\<langle\>|a<rsub|2>,b<rsub|2>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|1,n>=<around*|\<lceil\>|a<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>
    </equation*>

    so we know that

    <\equation*>
      <around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>=<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-add><rsub|n>|\<rrbracket\>><around*|\<langle\>|c,<around*|\<langle\>|a<rsub|2>,b<rsub|2>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|1,n>
    </equation*>

    Let us define <math|c<rsub|0>> and <math|r<rsub|0>> such that
    <math|<around*|\<langle\>|c<rsub|0>,r<rsub|0>|\<rangle\>>\<assign\><around*|\<llbracket\>|<math-ss|full-add><rsub|n>|\<rrbracket\>><around*|\<langle\>|c,<around*|\<langle\>|a<rsub|2>,b<rsub|2>|\<rangle\>>|\<rangle\>>>.
    Thus we have that

    <\eqnarray*>
      <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|<around*|\<langle\>|c<rsub|0>,r<rsub|0>|\<rangle\>>|\<rceil\>><rsub|1,n>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|c<rsub|0>|\<rceil\>><rsub|1>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|0>|\<rceil\>><rsub|n>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c<rsub|0>|\<rceil\>><rsub|1>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|0>|\<rceil\>><rsub|n>>>>>
    </eqnarray*>

    Again, by our inductive hypothesis, we have that

    <\equation*>
      <around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-add><rsub|n>|\<rrbracket\>><around*|\<langle\>|c<rsub|0>,<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|1,n>=<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c<rsub|0>|\<rceil\>><rsub|1>
    </equation*>

    therefore we have that

    <\equation*>
      <around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>=<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-add><rsub|n>|\<rrbracket\>><around*|\<langle\>|c<rsub|0>,<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|1,n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|2>|\<rceil\>><rsub|n>
    </equation*>

    Let us define <math|c<rsub|1>> and <math|r<rsub|1>> such that
    <math|<around*|\<langle\>|c<rsub|1>,r<rsub|1>|\<rangle\>>\<assign\><around*|\<llbracket\>|<math-ss|full-add><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,c<rsub|0>|\<rangle\>>>.
    Thus we have that

    <\eqnarray*>
      <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|c<rsub|1>,r<rsub|1>|\<rangle\>>|\<rceil\>><rsub|1,n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|0>|\<rceil\>><rsub|n>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|0>|\<rceil\>><rsub|n>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>\<cdot\>2<rsup|2*n>+<around*|\<lceil\>|r<rsub|1>|\<rceil\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|0>|\<rceil\>><rsub|n><eq-number><label|full-adder-RHS>>>>>
    </eqnarray*>

    Now let us consider the left hand side of equation
    <reference|full-adder-spec>. By the definition and semantics of
    <math|<math-ss|full-adder><rsub|2*n>> we have that

    <\eqnarray*>
      <tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|full-add><rsub|2*n>|\<rrbracket\>><around*|\<langle\>|c,<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>,<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rangle\>>|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>
      \<vartriangle\> <around*|(|<math-ss|IIH> \<vartriangle\>
      <math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|\<circ\>>|<cell|<around*|\<llbracket\>|<math-ss|IIH>
      \<vartriangle\> <around*|(|<math-ss|IOH> \<vartriangle\>
      <math-ss|OH>;<math-ss|full-add><rsub|n>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|\<circ\>>|<cell|<around*|\<llbracket\>|<math-ss|drop>
      <around*|(|<math-ss|OOH> \<vartriangle\> <math-ss|IOH>|)>
      \<vartriangle\> <around*|(|<math-ss|OH> \<vartriangle\> <math-ss|drop>
      <around*|(|<math-ss|OIH> \<vartriangle\>
      <math-ss|IIH>|)>;<math-ss|full-add><rsub|n>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|c,<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>,<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>
      \<vartriangle\> <around*|(|<math-ss|IIH> \<vartriangle\>
      <math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|\<circ\>>|<cell|<around*|\<llbracket\>|<math-ss|IIH>
      \<vartriangle\> <around*|(|<math-ss|IOH> \<vartriangle\>
      <math-ss|OH>;<math-ss|full-add><rsub|n>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,<around*|\<llbracket\>|<math-ss|full-add><rsub|n>|\<rrbracket\>><around*|\<langle\>|c,<around*|\<langle\>|a<rsub|2>,b<rsub|2>|\<rangle\>>|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>
      \<vartriangle\> <around*|(|<math-ss|IIH> \<vartriangle\>
      <math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|\<circ\>>|<cell|<around*|\<llbracket\>|<math-ss|IIH>
      \<vartriangle\> <around*|(|<math-ss|IOH> \<vartriangle\>
      <math-ss|OH>;<math-ss|full-add><rsub|n>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,<around*|\<langle\>|c<rsub|0>,r<rsub|0>|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>
      \<vartriangle\> <around*|(|<math-ss|IIH> \<vartriangle\>
      <math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|r<rsub|0>,<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|c<rsub|0>,<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>
      \<vartriangle\> <around*|(|<math-ss|IIH> \<vartriangle\>
      <math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|r<rsub|0>,<around*|\<langle\>|c<rsub|1>,r<rsub|1>|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<langle\>|c<rsub|1>,<around*|\<langle\>|r<rsub|1>,r<rsub|0>|\<rangle\>>|\<rangle\>>>>>>
    </eqnarray*>

    Therefore we have that

    <\eqnarray*>
      <tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-add><rsub|2*n>|\<rrbracket\>><around*|\<langle\>|c,<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>,<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|1,2*n>>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|c<rsub|1>,<around*|\<langle\>|r<rsub|1>,r<rsub|0>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|1,2*n>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>\<cdot\>2<rsup|2*n>+<around*|\<lceil\>|<around*|\<langle\>|r<rsub|1>,r<rsub|0>|\<rangle\>>|\<rceil\>><rsub|2*n>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>\<cdot\>2<rsup|2*n>+<around*|\<lceil\>|r<rsub|1>|\<rceil\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|0>|\<rceil\>><rsub|n><eq-number><label|full-adder-LHS>>>>>
    </eqnarray*>

    Together equations <reference|full-adder-RHS> and
    <reference|full-adder-LHS> show that the right hand side and left hand
    side of equation <reference|full-adder-spec> are equal, as required.
  </proof>

  Computer verified versions of theses proofs can be found in the Coq library
  (see Section<nbsp><reference|ss:coqArith>).

  With a full adder we can recursively build full multipliers.

  <\render-code>
    <math|<math-ss|full-multiply><rsub|1>\<of\><around*|(|<2>\<times\><2>|)>\<times\><around*|(|<2>\<times\><2>|)>\<vdash\><2><rsup|2>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-multiply><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|take>
    <around*|(|<math-ss|cond> <math-ss|iden> <math-ss|false>|)>
    \<vartriangle\> <math-ss|IH>;<math-ss|full-add><rsub|1>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|full-multiply><rsub|2*n>\<of\><around*|(|<2><rsup|2*n>\<times\><2><rsup|2*n>|)>\<times\><around*|(|<2><rsup|2*n>\<times\><2><rsup|2*n>|)>\<vdash\><2><rsup|4*n>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-multiply><rsub|2*n>>>|<cell|:=>|<cell|<math|<math-ss|take>
    <around*|(|<math-ss|OOH> \<vartriangle\> <around*|(|<math-ss|IOH>
    \<vartriangle\> <math-ss|OIH>|)>|)>>>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|(<math|<around*|(|<math-ss|take>
    <around*|(|<math-ss|OOH> \<vartriangle\> <math-ss|IIH>|)> \<vartriangle\>
    <math-ss|drop> <around*|(|<math-ss|OOH> \<vartriangle\>
    <math-ss|IOH>|)>;<math-ss|full-multiply><rsub|n>|)>>>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|<math|<around*|(|<math-ss|take>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IIH>|)> \<vartriangle\>
    <math-ss|drop> <around*|(|<math-ss|OIH> \<vartriangle\>
    <math-ss|IOH>|)>;<math-ss|full-multiply><rsub|n>|)>>)>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|take>
    <around*|(|<math-ss|OH> \<vartriangle\>
    <math-ss|IOH>|)>>>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|<math|<around*|(|<math-ss|drop>
    <around*|(|<math-ss|OOH> \<vartriangle\> <math-ss|IIH>|)> \<vartriangle\>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|drop>
    <around*|(|<math-ss|OIH> \<vartriangle\>
    <math-ss|IOH>|)>;<math-ss|full-multiply><rsub|n>|)>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<around*|(|<math-ss|OH>
    \<vartriangle\> <math-ss|drop> <around*|(|<math-ss|IOH> \<vartriangle\>
    <math-ss|OOH>|)>;<math-ss|full-multiply><rsub|n>|)> \<vartriangle\>
    <math-ss|drop> <around*|(|<math-ss|IIH> \<vartriangle\>
    <math-ss|OIH>|)>>>>>>>>>>>>
  </render-code>

  \;

  We can prove that the full multipliers meet the following specifications.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-multiply><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,<around*|\<langle\>|c,d|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2*n>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|n>\<cdot\><around*|\<lceil\>|b|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|n>+<around*|\<lceil\>|d|\<rceil\>><rsub|n>>>>>
  </eqnarray*>

  \;

  <with|color|red|TODO: Notes on trade-offs between efficiency and
  simplicity.>

  <subsection|Bitwise Operations>

  <subsection|SHA-256>

  The official standard for the SHA-2 family, which includes SHA-256, can be
  found in the <hlink|FIPS PUB 180-4: Secure Hash Standard
  (SHS)|http://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf><nbsp><cite|sha>.
  We define the SHA-256 function, <math|SHA256<rsub|<2>>\<of\><2><rsup|\<ast\>>\<rightarrow\><2><rsup|256>>,
  as a function from bit strings to a 256-bit word. Technically, SHA-256 is
  restricted to inputs <math|l\<of\><2><rsup|\<ast\>>> where
  <math|<around*|\||l|\|>\<less\>2<rsup|64>>.

  The SHA-256 hash function is composed from two components, a padding
  function <math|SHA256<rsub|Pad>\<of\><2><rsup|\<ast\>>\<rightarrow\><around*|(|<2><rsup|512>|)><rsup|+>>,
  which appends padding and length data to produce a (non-empty) sequence of
  blocks of 512 bits, and the Merkle--Damgård construction
  <math|SHA256<rsub|MD>\<of\><2><rsup|256>\<times\><around*|(|<2><rsup|512>|)><rsup|\<ast\>>\<rightarrow\><2><rsup|256>>.

  <\equation*>
    SHA256<rsub|<2>><around*|(|l|)>=SHA256<rsub|MD><around*|\<langle\>|SHA256<rsub|IV>,\<eta\><rsup|S><around*|(|SHA256<rsub|Pad><around*|(|l|)>|)>|\<rangle\>>
  </equation*>

  where <math|SHA256<rsub|IV>\<of\><2><rsup|256>> is the SHA-256 initial
  value and <math|\<eta\><rsup|S><rsub|A<rsup|+>>\<of\>A<rsup|+>\<rightarrow\>A<rsup|\<ast\>>>
  formally converts a non-empty list to a regular list.

  The <math|SHA256<rsub|MD>> function is a left fold using the SHA-256 block
  compression function <math|SHA256<rsub|Block>\<of\><2><rsup|256>\<times\><2><rsup|512>\<rightarrow\><2><rsup|256>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|SHA256<rsub|MD><around*|\<langle\>|h,\<epsilon\>|\<rangle\>>>|<cell|\<assign\>>|<cell|h>>|<row|<cell|SHA256<rsub|MD><around*|\<langle\>|h,b\<blacktriangleleft\>l|\<rangle\>>>|<cell|\<assign\>>|<cell|SHA256<rsub|MD><around*|\<langle\>|SHA256<rsub|Block><around*|\<langle\>|h,b|\<rangle\>>,l|\<rangle\>>>>>>
  </eqnarray*>

  The block compression function <math|SHA256<rsub|Block>\<of\><2><rsup|256>\<times\><2><rsup|512>\<rightarrow\><2><rsup|256>>
  is a function whose type fits in Simplicity's framework. We can create a
  core Simplicity term <math|<math-ss|sha256-block>\<of\><2><rsup|256>\<times\><2><rsup|512>\<vdash\><2><rsup|256>>
  that implements this function

  <\equation*>
    <around*|\<llbracket\>|<math-ss|sha256-block>|\<rrbracket\>>=SHA256<rsub|Block>
  </equation*>

  We can also define SHA-256's initial value
  <math|<math-ss|sha256-iv>\<of\><value|1>\<vdash\><2><rsup|256>>.

  <\equation*>
    <around*|\<llbracket\>|<math-ss|sha256-iv>|\<rrbracket\>><around*|\<langle\>||\<rangle\>>=SHA256<rsub|IV>
  </equation*>

  Beyond defining the block compression function in the Simplicity language,
  we will also be using the SHA-256 hash function elsewhere in this
  specification. In practice, SHA-256 is applied to byte strings rather than
  bit strings. To this end, we define the variant
  <math|SHA256<rsub|<2><rsup|8>>\<of\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>\<rightarrow\><2><rsup|256>>.

  <\equation*>
    SHA256<rsub|<2><rsup|8>>\<assign\>SHA256<rsub|<2>>\<circ\>\<mu\><rsup|\<ast\>>\<circ\><around*|(|\<iota\><rsup|<2><rsup|8>><rsub|<2><rsup|\<ast\>>>|)><rsup|\<ast\>>
  </equation*>

  where <math|\<iota\><rsup|<2><rsup|8>><rsub|<2><rsup|\<ast\>>>\<of\><2><rsup|8>\<rightarrow\><2><rsup|\<ast\>>>
  formally converts a byte to a bit string (in big endian format).

  <\equation*>
    \<iota\><rsup|<2><rsup|8>><rsub|<2><rsup|\<ast\>>><around*|\<langle\>|<around*|\<langle\>|<around*|\<langle\>|b<rsub|0>,b<rsub|1>|\<rangle\>>,<around*|\<langle\>|b<rsub|2>,b<rsub|3>|\<rangle\>>|\<rangle\>>,<around*|\<langle\>|<around*|\<langle\>|b<rsub|4>,b<rsub|5>|\<rangle\>>,<around*|\<langle\>|b<rsub|6>,b<rsub|7>|\<rangle\>>|\<rangle\>>|\<rangle\>>\<assign\>b<rsub|0>\<blacktriangleleft\>b<rsub|1>\<blacktriangleleft\>b<rsub|2>\<blacktriangleleft\>b<rsub|3>\<blacktriangleleft\>b<rsub|4>\<blacktriangleleft\>b<rsub|5>\<blacktriangleleft\>b<rsub|6>\<blacktriangleleft\>b<rsub|7>\<blacktriangleleft\>\<epsilon\>
  </equation*>

  Since the <math|SHA256<rsub|<2><rsup|8>>> variant is so commonly used, we
  will write it unadorned as simply <math|SHA256>.

  <subsubsection|Tagged Hashes>

  BIP-340, BIP-341 used a ``tagged-hash'' format to help avoid message
  collisions between different message variants. We adopt the same format
  here to avoid message collisions within a Simplicity application and we
  hope to avoid message collision across various applications.

  The tagged hash format begins every message with one block prefix which
  indicate the variant, or type of digest data being hashed. This first block
  consists of the SHA-256 digest of a string repeated twice. \ Given a byte
  string <math|t\<of\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>>, we can
  defined the tagged hash of bit strings,
  <math|SHA256<rsup|t><rsub|<2>>\<of\><2><rsup|\<ast\>>\<rightarrow\><2><rsup|256>>,
  and byte strings, \ <math|SHA256<rsup|t><rsub|<2><rsup|8>>\<of\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>\<rightarrow\><2><rsup|256>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|SHA256<rsup|t><rsub|<2>><around*|(|x|)>>|<cell|\<assign\>>|<cell|SHA256<rsub|<2>><around*|(|\<mu\><rsup|\<ast\>><around*|(|<around*|(|\<iota\><rsup|<2><rsup|8>><rsub|<2><rsup|\<ast\>>>|)><rsup|\<ast\>><around*|(|p\<cdummy\>p|)>|)>\<cdummy\>x|)>>>|<row|<cell|SHA256<rsup|t><rsub|<2><rsup|8>><around*|(|x|)>>|<cell|\<assign\>>|<cell|SHA256<rsub|<2><rsup|8>><around*|(|p\<cdummy\>p\<cdummy\>x|)>>>|<row|<cell|>|<cell|where>|<cell|p\<assign\>BE<rsub|256><around*|(|SHA256<rsub|<2><rsup|8>><around*|(|t|)>|)>>>>>
  </eqnarray*>

  \ We can compute the SHA-256 midstate after compressing this first block
  containing the prefix tag.

  <\equation*>
    SHA256<rsup|t><rsub|IV>\<assign\>SHA256<rsub|Block><around*|\<langle\>|SHA256<rsub|IV>,\<Delta\><around*|(|SHA256<rsub|<2><rsup|8>><around*|(|t|)>|)>|\<rangle\>>
  </equation*>

  \;

  <subsection|Elliptic Curve Operations on secp256k1>

  The Standards for Efficient Cryptography (SEC) documents have recommend
  modular elliptic curve parameters including the secp256k1
  curve<nbsp><cite|sec2>, which is used by Bitcoin's EC-DSA signature scheme
  and the proposed EC-Schnorr scheme.

  Most points on an elliptic curve, such as secp256k1, consist of a pair of
  coordinates from a specified finite field. In the case of secp256k1, the
  finite field is the prime field <math|\<bbb-F\><rsub|p><rsub|>> where
  <math|p\<assign\>2<rsup|256>-4294968273>. The elliptic curve for secp256k1
  consists of the points <math|<around*|\<langle\>|x,y|\<rangle\>>>
  satisfying the equation <math|y<rsup|2>\<equiv\>x<rsup|3>+7 <around*|(|mod
  p|)>>, plus an additional ``point at infinity'', which we will write as
  <math|\<cal-O\>>. It turns out that elliptic curves can be given a group
  structure via ``geometry'', where any three points on the curve that are
  co-linear sum to 0 under this group structure, and where <math|\<cal-O\>>
  is the group's identity element. We have to be careful to count lines
  ``tangent'' to the curve as passing through the same point twice, and count
  vertical lines as passing through <math|\<cal-O\>>. This group structure is
  Abelian, and therefore can also be viewed as a
  <math|\<bbb-Z\><rsub|n>>-module<\footnote>
    Mathematically, we actually have a 1-dimensional vector space; however
    determining the linear dependence between two vectors is presumed to be
    infeasible. Indeed, the security properties of the elliptic curve depends
    on this being infeasible. For this reason, it is more useful to think of
    this structure as a module rather than as a vector space.
  </footnote> where <math|n \<assign\> 2<rsup|256>-432420386565659656852420866394968145599>
  is the order of this elliptic curve. This <math|\<bbb-Z\><rsub|n>>-module
  structure allows us to talk about ``adding'' two points of the elliptic
  curve, and scaling a point by a factor from <math|\<bbb-Z\><rsub|n>>.

  Because the order of the elliptic curve, <math|n>, is a prime number, every
  non-<math|\<cal-O\>> element generates the entire curve (through scalar
  multiplication). The specification for secp256k1 comes with a reference
  generator, <math|\<cal-G\>>, which is defined as the following point.

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<cal-G\>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|55066263022277343669578718895168534326250603453777594175500187360389116729240<next-line>,32670510020758816978083085130507043184471273380659243275938904335757337482424|\<rangle\>>>>>>
  </eqnarray*>

  <subsubsection|libsecp256k1>

  The libsecp256k1 library<nbsp><cite|libsecp256k1> is a C implementation of
  optimized functions on this elliptic curve. This library has two variants
  for the representation of elliptic curve point values. The affine
  coordinate representation consists of a pair of field elements, and a flag
  to indicate the value <math|\<cal-O\>> (in which case the coordinate values
  are ignored). The Jacobian coordinate representation consists of a triple
  of field elements, and a flag to indicate the value <math|\<cal-O\>> (in
  which case the coordinates are ignored).

  A point in Jacobian coordinates, <math|<around*|\<langle\>|x,y,z|\<rangle\>>>
  is defined to be on the elliptic curve when

  <\equation*>
    y<rsup|2>\<equiv\>x<rsup|3>+7z<rsup|6> <around*|(|mod p|)>
  </equation*>

  and two points in Jacobian coordinates are equivalent,
  <math|<around*|\<langle\>|x<rsub|0>,y<rsub|0>,z<rsub|0>|\<rangle\>>\<asymp\><around*|\<langle\>|x<rsub|1>,y<rsub|1>,z<rsub|1>|\<rangle\>>>,
  when

  <\equation*>
    x<rsub|0>*z<rsub|1><rsup|2>\<equiv\>x<rsub|1>*z<rsub|0><rsup|2>
    <around*|(|mod p|)><text| and >y<rsub|0>*z<rsub|1><rsup|3>\<equiv\>y<rsub|1>*z<rsub|0><rsup|3>
    <around*|(|mod p|)><text|.>
  </equation*>

  A point in Jacobian coordinates, <math|<around*|\<langle\>|x,y,z|\<rangle\>>>
  represents the curve point <math|<around*|\<langle\>|x*z<rsup|-2>,y*z<rsup|-3>|\<rangle\>>>
  in affine coordinates when <math|z\<neq\>0>. In particular, the point
  <math|<around*|\<langle\>|x,y,1|\<rangle\>>> in Jacobian coordinates
  represents the point <math|<around*|\<langle\>|x,y|\<rangle\>>> in affine
  coordinates. The same point has multiple representations in Jacobian
  coordinates, however, even the affine coordinate representation is
  redundant because the underlying field representation is itself redundant.

  Normally the point at infinity would be represented by
  <math|<around*|\<langle\>|a<rsup|2>,a<rsup|3>,0|\<rangle\>>> in Jacobian
  coordinates for any <math|a\<in\>\<bbb-F\><rsub|p>>; however this is not
  done in libsecp256k1. Instead a flag is used to represent the point at
  infinity (and the coordinates are ignored when this flag is set). Testing
  if a field element is equivalent to 0 is a non-trivial operation, so using
  a flag like this may be sensible.

  The various group and <math|\<bbb-Z\><rsub|n>>-module operations are
  implemented efficiently, again subject to various specific preconditions on
  their inputs. In particular, the operation for forming linear combinations
  of the form

  <\equation*>
    <big|sum><rsub|i=0><rsup|k>n<rsub|\<cal-A\><rsub|i>>*\<cal-A\><rsub|i>+n<rsub|\<cal-G\>>*\<cal-G\>
  </equation*>

  is supported using an algorithm known as Shamir's trick, where
  <math|n<rsub|\<cal-A\><rsub|i>>\<of\>\<bbb-Z\><rsub|n>>,
  <math|n<rsub|\<cal-G\>>\<of\>\<bbb-Z\><rsub|n>>, and
  <math|\<cal-A\><rsub|i>> are points on the elliptic curve.

  <subsubsection|libsecp256k1 in Simplicity>

  The primary application for Simplicity is to implement computation for
  public validation. In implementing cryptographic operations in Simplicity,
  we have no need to worry about constant-time implementations, nor securing
  private key material because Simplicity's application only processes public
  data.

  When it comes to implementing elliptic curve operations in Simplicity, we
  do face one problem. In order for elliptic curve operations to be fast, we
  need a representation of field elements and curve points that have
  redundant representations, but then the choice of which specific
  representative returned by Simplicity expressions becomes consensus
  critical.

  We see three possible ways of addressing this problem:

  <\enumerate-numeric>
    <item>We can define minimal Simplicity types that can represent field
    elements and elliptic curve points and return values in normal form after
    every elliptic curve operation.

    <item>We can define Simplicity types that can represent field elements
    and elliptic curve points with redundant representations and specify
    precisely which representative is the result of each elliptic curve
    operation.

    <item>We can extend Simplicity with abstract data types for field
    elements and elliptic curve points and enforce data abstraction in the
    elliptic curve operations.
  </enumerate-numeric>

  Option 1 would make it easy for developers to implement elliptic curve jets
  (see Section<nbsp><inactive|<reference|<with|color|red|TODO>>>) that
  short-cut the interpretation of Simplicity's elliptic curve operations by
  running native code instead. The native code for these jets can be
  implemented by any reasonable algorithm, and the results normalized. The
  problem with this option is that computing the normal form of elliptic
  curve points is an expensive operation. In particular, normalizing a point
  in Jacobian coordinates requires computing a modular inverse, which is a
  very expensive operation compared to the other field operations.

  Option 2 means we must ensure that the native code for jets returns exactly
  the same representative that the Simplicity expression it replaces would
  have produced. Even libsecp256k1 does not guarantee that different versions
  of the library will return the same representatives for its basic elliptic
  curve operations, so Simplicity jets would not be able to keep up with
  libsecp256k1 updates.

  Option 3 would let us change the underlying representations of elliptic
  curve values, allowing us to use any version of any secp256k1 library.
  However, it would extend the scope of Simplicity beyond what we are willing
  to do.

  We have chosen to go with option 2. We have reimplemented the exact same
  algorithms for field and elliptic curve operations that the most recent
  release of libsecp256k1 uses as of the time of this writing, including
  computing of linear combinations of the form

  <\equation*>
    n<rsub|\<cal-A\><rsub|>>*\<cal-A\>+n<rsub|\<cal-G\>>*\<cal-G\>
  </equation*>

  which is used for Schnorr signature validation. Our jets will be tied to
  this specific version of libsecp256k1, and the commitment Merkle root (see
  Section<nbsp><reference|ss:cmr>) captures the formal specification of the
  functional behaviour of our jets. The libsecp256k1 is already reasonably
  mature, so we are not expecting to lose out too much by missing future
  advances. When there are major improvements, new versions of Simplicity
  jets could be substituted in by using a versioning mechanism for
  Simplicity.

  In Simplicity, we represent a field element by the type

  <\equation*>
    FE\<assign\><2><rsup|256>
  </equation*>

  and a value <math|a\<of\>FE> represents the field element

  <\equation*>
    <around*|\<lceil\>|a|\<rceil\>><rsub|FE>\<assign\><around*|\<lceil\>|a|\<rceil\>><rsub|256>
    <around*|(|mod p|)><text|.>
  </equation*>

  We represent non-<math|\<cal-O\>> points on the secp256k1 elliptic curve in
  affine coordinates by the type

  <\equation*>
    GE\<assign\>FE\<times\>FE
  </equation*>

  and a value <math|<around*|\<langle\>|x,y|\<rangle\>>\<of\>GE> represents
  the point

  <\equation*>
    <around*|\<lceil\>|<around*|\<langle\>|x,y|\<rangle\>>|\<rceil\>><rsub|GE>\<assign\><around*|\<langle\>|<around*|\<lceil\>|x|\<rceil\>><rsub|FE>,<around*|\<lceil\>|y|\<rceil\>><rsub|FE>|\<rangle\>><text|.>
  </equation*>

  We also represent points on the secp256k1 elliptic curve in Jacobian
  coordinates by the type

  <\equation*>
    GEJ\<assign\>GE\<times\>FE
  </equation*>

  and a value <math|<around*|\<langle\>|<around*|\<langle\>|x,y|\<rangle\>>,z|\<rangle\>>>
  represents the point

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|<around*|\<langle\>|x,y|\<rangle\>>,z|\<rangle\>>|\<rceil\>><rsub|GEJ>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|<around*|\<lceil\>|x|\<rceil\>><rsub|FE>\<cdot\><around*|\<lceil\>|z|\<rceil\>><rsub|FE><rsup|-2>
    <around*|(|mod p|)>,<around*|\<lceil\>|y|\<rceil\>><rsub|FE>\<cdot\><around*|\<lceil\>|z|\<rceil\>><rsub|FE><rsup|-3>
    <around*|(|mod p|)>|\<rangle\>><htab|5mm><text|when
    <math|<around*|\<lceil\>|z|\<rceil\>><rsub|FE> \<nequiv\>0 <around*|(|mod
    p|)>>>>>|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|<around*|\<langle\>|x,y|\<rangle\>>,z|\<rangle\>>|\<rceil\>><rsub|GEJ>>|<cell|\<assign\>>|<cell|\<cal-O\><htab|5mm><text|when
    <math|<around*|\<lceil\>|z|\<rceil\>><rsub|FE>\<equiv\>0 <around*|(|mod
    p|)>> and ><around*|\<lceil\>|y|\<rceil\>><rsub|FE><rsup|2>\<equiv\><around*|\<lceil\>|x|\<rceil\>><rsub|FE><rsup|3>
    <around*|(|mod p|)><text|.>>>>>
  </eqnarray*>

  The translation between libsecp256k1's affine coordinate representation of
  elliptic curve points and Simplicity's <math|GE> is straightforward except
  that Simplicity's <math|GE> type has no flag and cannot represent the
  <math|\<cal-O\>> point. The translation between libsecp256k1's Jacobian
  coordinate representation of elliptic curve points and Simplicity's
  <math|GEJ> type is mostly straight forward, however the <math|GEJ> type
  represents the <math|\<cal-O\>> point using a z-coordinate representing 0,
  while libsecp256k1 uses a flag to represent the <math|\<cal-O\>> point.

  The Simplicity implementation of libsecp256k1 is designed so that
  libsecp256k1 can be used as jets for these Simplicity expressions. As such,
  the Simplicity expressions are designed to mimic the exact behaviour of a
  specific version of libsecp256k1's elliptic curve functions. For inputs of
  particular representations of point in Jacobian coordinates, the Simplicity
  expression returns the exact same representative for its result as
  libsecp256k1. If an off-curve point is passed to a libsecp256k1 function,
  the Simplicity code again computes the same result that the libsecp256k1
  function does.

  The only subtle point with using libsecp256k1 for jets lies in the
  different representation of <math|\<cal-O\>>. The inputs and outputs of
  operations need to be suitable translated between the two representations.
  However, this can be done as part of the marshalling code for the jets, and
  the Simplicity expressions are written with this in mind.

  <subsubsection|Schnorr Signature Validation>

  With elliptic curve operations defined, we are able to implement Schnorr
  signature validation in accordance with the BIP-0340
  specification<nbsp><cite|bip-0340>. We define Simplicity types for the
  formats of x-only public keys, <math|PubKey>; messages, <math|Msg>; and
  Schnorr signatures, <math|Sig>, below.

  <\eqnarray*>
    <tformat|<table|<row|<cell|PubKey>|<cell|\<assign\>>|<cell|<2><rsup|256>>>|<row|<cell|Msg>|<cell|\<assign\>>|<cell|<2><rsup|256>>>|<row|<cell|Sig>|<cell|\<assign\>>|<cell|<2><rsup|512>>>>>
  </eqnarray*>

  The <math|PubKey> type is an x-coordinate of a point whoes y-coordinate's
  least significant bit is even. A <math|Msg> value <math|m> represents the
  byte-string <math|BE<rsub|256><around*|(|m|)>> for a Schnorr signature's
  message, and a <math|Sig> value <math|a> represents the byte-string
  <math|BE<rsub|512><around*|(|a|)>> for a Schnorr signature.

  We have implemented a core Simplicity expression to check a Schnorr
  signature for a public key on a given message:

  <\equation*>
    <math-ss|bip0340-check>\<of\><around*|(|PubKey\<times\>Msg|)>\<times\>Sig\<vdash\><2>
  </equation*>

  The semantics are such that <math|<around*|\<llbracket\>|<math-ss|bip0340-check>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|p,m|\<rangle\>>,s|\<rangle\>>=<math-tt|1><rsub|<2>>>
  only when the values that the inputs represents satisfy the verification
  conditions of the BIP-0340 specification.

  <section|Completeness Theorem>

  General purpose programming languages are famously incomplete because there
  are functions that are uncomputable, the halting problem being the most
  famous of these. Core Simplicity is even more limited that these general
  purpose programming languages because its denotational semantics are
  limited to functions from finite types to finite types.

  However, we can ask the question, is every function from a finite type to a
  finite type expressible in core Simplicity? This question is answered by
  the following completeness theorem.

  <\theorem>
    <label|thm:CSCT>Core Simplicity Completeness Theorem. For any Simplicity
    types <math|A> and <math|B> and any function <math|f:A\<rightarrow\>B>,
    there exists some core Simplicity term <math|t> such that for all
    <math|a:A>,

    <\equation*>
      <around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>=f<around*|(|a|)>
    </equation*>
  </theorem>

  This result is possible because these functions are all finitary and can
  be, in principle, expressed as a large lookup table. It is possible to
  encode these lookup tables with Simplicity expressions. The formal proof of
  this theorem can be found in the Coq library (see
  Section<nbsp><reference|ss:coqInitial>).

  It is worth emphasizing that this result is a purely theoretical result
  that shows that core Simplicity is fully expressive for its domain; it is
  completely impractical to generate Simplicity expressions this way as many
  expressions would be astronomical in size. Thus we can view Simplicity
  programming as an exercise in compression: how can we take advantage of the
  structure within computations to express our functions succinctly.

  One practical variant of the core Simplicity completeness theorem is that
  for any value of a Simplicity type <math|b\<of\>B>, the constant function
  <math|\<lambda\>_\<point\>b\<of\>A\<rightarrow\>B> can be realized by a
  Simplicity expression. We call the function that constructs this term,
  <math|<math-ss|scribe><rsub|A,B><around*|(|b|)>\<of\>A\<vdash\>B>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<math-ss|scribe><rsub|A,<1>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|<math-ss|unit>>>|<row|<cell|<math-ss|scribe><rsub|A,B+C><around*|(|<injl-long|B|C|<around*|(|b|)>>|)>>|<cell|\<assign\>>|<cell|<math-ss|injl>
    <around*|(|<math-ss|scribe><rsub|A,B><around*|(|b|)>|)>>>|<row|<cell|<math-ss|scribe><rsub|A,B+C><around*|(|<injr-long|B|C|<around*|(|c|)>>|)>>|<cell|\<assign\>>|<cell|<math-ss|injr>
    <around*|(|<math-ss|scribe><rsub|A,C><around*|(|c|)>|)>>>|<row|<cell|<math-ss|scribe><rsub|A,B\<times\>C><around*|\<langle\>|b,c|\<rangle\>>>|<cell|\<assign\>>|<cell|<math-ss|scribe><rsub|A,B><around*|(|b|)>
    \<vartriangle\> <math-ss|scribe><rsub|A,C><around*|(|c|)>>>>>
  </eqnarray*>

  <\theorem>
    For all Simplicity types <math|A> and <math|B>, and for all values
    <math|a\<of\>A> and <math|b\<of\>B>, <\equation*>
      <around*|\<llbracket\>|<math-ss|scribe><rsub|A,B><around*|(|b|)>|\<rrbracket\>><around*|(|a|)>=b<text|.>
    </equation*>
  </theorem>

  <section|Operational Semantics>

  The denotational semantics of Simplicity determine the functional behaviour
  of expressions. However, they are not suitable for determining the
  computation resources needed to evaluate expressions. For this reason we
  define an operational semantics for Simplicity via an abstract machine we
  call the <dfn|Bit Machine>.

  <subsection|Representing Values as Cell
  Arrays><label|ss:RepresentingValuesAsCellArrays>

  <assign|carr|<macro|x|<verbatim|[<arg|x>]>>><assign|cearr|<macro|x|<verbatim|[<arg|x><underline|]>>>><assign|rep|<macro|x|y|<math|\<ulcorner\><arg|x>\<urcorner\><rsub|<arg|y>>>>>Values
  in the Bit Machine are represented by arrays of cells where each cell
  contains one of three values: a <verbatim|0> value, a <verbatim|1> value,
  or a <verbatim|?> value which we call an undefined value. We write an array
  of cells by enclosing a sequence of cells with square brackets (e.g.
  <carr|1?0>). We denote the length of an array using
  <math|<around*|\||\<cdummy\>|\|>>. For example,
  <math|<around*|\||<carr|1?0>|\|>=3>. The concatenation of two arrays,
  <math|a> and <math|b> is denoted by <math|a\<cdot\>b>, and replication of
  an array <math|n> times is denoted by exponentiation, <math|a<rsup|n>>.
  Sometimes we will omit the dot when performing concatenation.

  For any given type, we define the number of cells needed to hold values of
  that type using the following <math|bitSize> function.

  <\eqnarray*>
    <tformat|<table|<row|<cell|bitSize<around*|(|<value|1>|)>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|bitSize<around*|(|A+B|)>>|<cell|\<assign\>>|<cell|1+max<around*|(|bitSize<around*|(|A|)>,bitSize<around*|(|B|)>|)>>>|<row|<cell|bitSize<around*|(|A\<times\>B|)>>|<cell|\<assign\>>|<cell|bitSize<around*|(|A|)>+bitSize<around*|(|B|)>>>>>
  </eqnarray*>

  We define a representation of values of Simplicity types as arrays of cells
  as follows.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<rep|<around*|\<langle\>||\<rangle\>>|<value|1>>>|<cell|\<assign\>>|<cell|<carr|>>>|<row|<cell|<rep|<injl-long|A|B|<around*|(|a|)>>|A+B>>|<cell|\<assign\>>|<cell|<carr|0>\<cdot\><carr|?><rsup|padL<around*|(|A,B|)>>\<cdot\><rep|a|A>>>|<row|<cell|<rep|<injr-long|A|B|<around*|(|b|)>>|A+B>>|<cell|\<assign\>>|<cell|<carr|1>\<cdot\><carr|?><rsup|padR<around*|(|A,B|)>>\<cdot\><rep|b|B>>>|<row|<cell|<rep|<around*|\<langle\>|a,b|\<rangle\>>|A\<times\>B>>|<cell|\<assign\>>|<cell|<rep|a|A>\<cdot\><rep|b|B>>>>>
  </eqnarray*>

  The representation of values of a sum type are padded with undefined cells
  so that the representation has the proper length.

  <\eqnarray*>
    <tformat|<table|<row|<cell|padL<around*|(|A,B|)>>|<cell|\<assign\>>|<cell|max<around*|(|bitSize<around*|(|A|)>,bitSize<around*|(|B|)>|)>-bitSize<around*|(|A|)>>>|<row|<cell|padR<around*|(|A,B|)>>|<cell|\<assign\>>|<cell|max<around*|(|bitSize<around*|(|A|)>,bitSize<around*|(|B|)>|)>-bitSize<around*|(|B|)>>>>>
  </eqnarray*>

  <\theorem>
    Given any value of some Simplicity type, <math|a\<of\>A>, we have
    <math|<around*|\||<rep|a|A>|\|>=bitSize<around*|(|A|)>>.
  </theorem>

  <subsection|Bit Machine>

  A frame is a, possibly empty, cell array with a cursor referencing a cell
  in the array, which we denote using an underscore.

  <\equation*>
    <carr|0<underline|1>?10>
  </equation*>

  The cursor may also reference the end of the array, which we denote by
  marking the end of the array with an underscore.

  <\equation*>
    <cearr|01?10>
  </equation*>

  Frames can be concatenated with cell arrays either on the left or on the
  right without moving the cursor. Note that when concatenating a non-empty
  cell array onto the right hand side of a frame whose cursor is at the end
  of the frame, the cursor ends up pointing to the first cell of the added
  cell array.

  <\equation*>
    <cearr|01?10><carr|111??>=<carr|01?10<wide*|1|\<bar\>>11??>
  </equation*>

  <assign|emptyFrame|<math|<tiny|\<wedge\>>>>We will sometimes denote the
  empty frame, <math|<cearr|>>, with a small cursor, <value|emptyFrame>.

  The state of the Bit Machine consists of two non-empty stacks of frames: a
  read-frame stack and a write-frame stack. The top elements of the two
  stacks are called the <dfn|active read frame> and the <dfn|active write
  frame> respectively. The other frames are called inactive read-frames and
  inactive write-frames.

  <big-figure|<tabular|<tformat|<cwith|1|1|1|-1|cell-tborder|2px>|<cwith|5|5|1|-1|cell-bborder|2px>|<cwith|1|1|1|-1|cell-bborder|1px>|<table|<row|<cell|read
  frame stack>|<cell|write frame stack>>|<row|<cell|<carr|100<underline|1>1??110101000>>|<cell|<cearr|11??1101>>>|<row|<cell|<carr|<underline|0>000>>|<cell|<carr|111<underline|?>?>>>|<row|<cell|<cearr|>>|<cell|>>|<row|<cell|<carr|<underline|1>0>>|<cell|>>>>>|Example
  state of the Bit Machine.>

  <assign|halted|<math|<op|\<boxtimes\>>>>Notationally we will write a stack
  of read frames as <math|r<rsub|n>\<vartriangleright\>\<ldots\>\<vartriangleright\>r<rsub|1>\<vartriangleright\>r<rsub|0>>,
  with <math|r<rsub|0>> as the active read frame. We will write a stack of
  write frames in the opposite order, as <math|w<rsub|0>\<vartriangleleft\>w<rsub|1>\<vartriangleleft\>\<ldots\>\<vartriangleleft\>w<rsub|m>>
  with <math|w<rsub|0>> as the active write frame. We write a state of the
  Bit Machine as <math|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>>
  where <math|\<Theta\>> is the (possibly empty) inactive read frame stack,
  <math|\<Xi\>> is the (possibly empty) inactive write frame stack,
  <math|r<rsub|0>> is the active read frame, and <math|w<rsub|0>> is the
  active write frame.<\footnote>
    The notation for the Bit Machine's state is intended to mimic the gap
    buffer used in our C implementation of the Bit Machine (see
    <with|color|red|TODO: C implementation>).
  </footnote> There is one additional state of the Bit Machine called the
  <dfn|halted> state, which we denote by <value|halted>.

  The Bit Machine has nine basic instructions that, when executed, transform
  the Bit Machine's state. We denote these basic instructions as
  <math|i\<of\>S<rsub|0>\<rightsquigarrow\>S<rsub|1>>, where <math|i> is the
  instructions's name, <math|S<rsub|0>> is a state of the Bit Machine before
  executing the instruction, and <math|S<rsub|1>> is the state of the machine
  after the successful execution of the instructions.

  <subsubsection|Frame Instructions>

  Our first three basic instructions, create, move, and delete active frames.

  <\eqnarray*>
    <tformat|<table|<row|<cell|newFrame<around*|(|n|)>>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|<emptyFrame><carr|?><rsup|n>\<vartriangleleft\>w<rsub|0>\<vartriangleleft\>\<Xi\>|]>>>|<row|<cell|moveFrame>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|<cearr|c<rsub|1>*\<cdots\>*c<rsub|n>>\<vartriangleleft\>w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<vartriangleright\><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>*c<rsub|n>>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>>>|<row|<cell|dropFrame>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\<vartriangleright\>r<rsub|0>\|\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\|\<Xi\>|]>>>>>
  </eqnarray*>

  Executing a <math|newFrame<around*|(|n|)>> instruction pushes a new frame
  of length <math|n> onto the write frame stack. This new frame has its
  cursor at the beginning of the frame and the entire frame is filled with
  undefined values. It is legal for the new frame to have length 0.

  Executing the <math|moveFrame> instruction moves the top frame of the write
  frame stack to the read frame stack. This instruction is only legal to
  execute when the cursor of the active write frame is at the end of the
  frame. The cursor is reset to the beginning of the frame when it is placed
  onto the read frame stack.

  Executing the <math|dropFrame> instruction removes the top frame of the
  read frame stack.

  <subsubsection|Active Write Frame Instructions>

  Our next three instructions operate on the active write frame.

  <\eqnarray*>
    <tformat|<table|<row|<cell|write<around*|(|0|)>>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<cdummy\><carr|<wide*|?|\<bar\>>><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<cdummy\><cearr|0><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>>|<row|<cell|write<around*|(|1|)>>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<cdummy\><carr|<wide*|?|\<bar\>>><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<cdummy\><cearr|1><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>>|<row|<cell|skip<around*|(|n|)>>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0><emptyFrame><carr|?><rsup|n+m>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<cdummy\><carr|?><rsup|n><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>>|<row|<cell|copy<around*|(|n|)>>|<cell|:>|<cell|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>*c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|n+m>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>*c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\><cearr|c<rsub|1>*\<cdots\>*c<rsub|n>><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>>>>
  </eqnarray*>

  Executing a <math|write<around*|(|b|)>> instruction writes a 0 or 1 to the
  active write frame and advances its cursor. Writing an undefined value
  using this instruction is not allowed. The cursor cannot be at the end of
  the frame.

  Executing a <math|skip<around*|(|n|)>> instruction advances the active
  write frame's cursor without writing any data. There must be sufficient
  number of cells after the cursor. The trivial instruction
  <math|skip<around*|(|0|)>> is legal and executing it is effectively a
  no-op.

  Executing a <math|copy<around*|(|n|)>> instruction copies the values of the
  <math|n> cells after the active read frame's cursor into the active write
  frame, advancing the write frame's cursor. The must be a sufficient number
  of cells after both the active read frame and active write frame's cursors.
  Note that undefined cell values are legal to copy. The trivial instruction
  <math|copy<around*|(|0|)>> is legal and executing it is effectively a
  no-op.

  <subsubsection|Active Read Frame Instructions>

  The next two instructions are used to manipulate the active read frame's
  cursor.

  <\equation*>
    fwd<around*|(|n|)>\<of\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>*c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><cearr|c<rsub|1>*\<cdots\>*c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>
  </equation*>

  <\equation*>
    bwd<around*|(|n|)>\<of\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><cearr|c<rsub|1>*\<cdots\>*c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>*c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>
  </equation*>

  Executing a <math|fwd<around*|(|n|)>> instructions moves the cursor on the
  active read frame forward, and executing a <math|bwd<around*|(|n|)>>
  instruction moves the cursor backwards. In both cases there must be
  sufficient number of cells before or after the cursor. The trivial
  instructions <math|fwd<around*|(|0|)>> and <math|bwd<around*|(|0|)>> are
  legal and executing them are effectively no-ops.

  <subsubsection|Abort Instruction>

  The final instruction of for the Bit Machine moves from any non-halted
  state into the halted state.

  <\equation*>
    abort\<of\><around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>\<rightsquigarrow\><halted>
  </equation*>

  This is the only way to enter the halted state, and once in the halted
  state no further instructions can be executed.

  <subsubsection|Bit Machine Programs>

  <assign|prog|<macro|x|p|y|<math|<arg|x><math-relation|\<#291C\>><arg|p>\<twoheadrightarrow\><arg|y>>>>The
  basic instructions of the Bit Machine are combined to produce programs that
  take the Bit Machine through a sequence of states. We write
  <prog|S<rsub|0>|k|S<rsub|1>> for a program, <math|k>, that, when executed,
  successfully transforms an initial state <math|S<rsub|0>> to the final
  state <math|S<rsub|1>>.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<cwith|1|1|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-col-span|2>|<table|<row|<cell|<prog|S|nop|S>>>>>>
  </with>

  We write <math|nop> for the trivial program with no instructions. The
  initial and final states are identical in this case.

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|i:S<rsub|0>\<rightsquigarrow\>S<rsub|1>>>>|<row|<cell|<prog|S<rsub|0>|i|S<rsub|1>>>>>>>
  </with>

  For every basic instruction there is a single instruction program whose
  initial and final states match those of the basic instruction.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<prog|S<rsub|0>|k<rsub|0>|S<rsub|1>>>|<cell|<prog|S<rsub|1>|k<rsub|1>|S<rsub|2>>>>>>>>>|<row|<cell|<prog|S<rsub|0>|k<rsub|0>;k<rsub|1>|S<rsub|2>>>>>>>
  </with>

  \;

  We write <math|k<rsub|0>;k<rsub|1>> for a sequence of two programs,
  <math|k<rsub|0>> and <math|k<rsub|1>>. The Bit Machine executes the two
  programs in turn, concatenating the sequence of states of the two programs.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|0|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0>|S<rsub|>>>>|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|0|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0>\|\|k<rsub|1>|S>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|1|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|1>|S>>>|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|1|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0>\|\|k<rsub|1>|S>>>>>>
  </with>

  We define <math|k<rsub|0>\|\|k<rsub|1>> as a deterministic choice between
  two programs, <math|k<rsub|0>> and <math|k<rsub|1>>. When executing a
  deterministic choice, the value under the active read frame's cursor
  decides which one of the two programs are executed. When encountering a
  deterministic choice, the active read frame's cursor must not be at the end
  of its array and the cell under the cursor must not be an undefined value.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<cwith|1|1|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-col-span|2>|<table|<row|<cell|<prog|<halted>|k|<halted>>>>>>>
  </with>

  Lastly, we stipulate that every program when executed from the halted state
  ignores all instructions and perform a no-op instead.

  Take care to note this difference between instructions and programs
  containing one instruction. A single instruction cannot be executed
  starting from the halted state, while a program that consists of a single
  instruction can be run starting from the halted state (however, it does
  nothing from this state).

  <\equation*>
    n\<star\>k\<assign\>fwd<around*|(|n|)>;k;bwd<around*|(|n|)>
  </equation*>

  The <math|n\<star\>k> notation (called ``bump'') is for a program that
  temporarily advances the active read frame's cursor when executing
  <math|k>.

  <\theorem>
    \;

    <\with|par-mode|center>
      <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><cearr|c<rsub|1>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><cearr|c<rsub|1>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>>>|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|n\<star\>k|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>c<rsub|n>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>>>>>>
    </with>

    \;
  </theorem>

  <subsubsection|Crashing the Bit Machine>

  Bit Machine programs are deterministic. Given a program <math|k> and an
  initial state <math|S<rsub|0>> there exists at most one state
  <math|S<rsub|1>> such that <prog|S<rsub|0>|k|S<rsub|1>>. However it is
  possible that there is no state <math|S<rsub|1>> such that
  <prog|S<rsub|0>|k|S<rsub|1>> given an initial state for a program. This
  happens when the Bit Machine is trying to execute a single instruction
  program, <math|i>, from a non-halted state where that instruction cannot
  legally execute from. This can also happen when a deterministic choice
  operation is encountered starting from a state where the active read
  frame's cursor is at the end of the frame, or is referencing and undefined
  value.

  When a program cannot execute to completion from a given initial state, we
  say that the Bit Machine crashes, or we say that the program crashes the
  Bit Machine. Crashing is distinct from halting. We will have a number of
  theorems that prove that a Bit Machine interpreting a Simplicity expression
  from a suitable initial state never crashes the Bit Machine; however in
  some of these cases the program may cause the Bit Machine to legitimately
  enter the halted state.

  <subsection|Executing Simplicity>

  We recursively translate a core Simplicity program,
  <math|t\<of\>A\<vdash\>B>, into a program for the Bit Machine,
  <math|<around*|\<llangle\>|t|\<rrangle\>>>, called the naive translation:

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<around*|\<llangle\>|<math-ss|iden><rsub|A>|\<rrangle\>>>|<cell|\<assign\>>|<cell|copy<around*|(|bitSize<around*|(|A|)>|)>>>|<row|<cell|<around*|\<llangle\>|<math-ss|comp><rsub|A,B,C>
    s t|\<rrangle\>>>|<cell|\<assign\>>|<cell|newFrame<around*|(|bitSize<around*|(|B|)>|)>>>|<row|<cell|>|<cell|;>|<cell|<around*|\<llangle\>|s|\<rrangle\>>>>|<row|<cell|>|<cell|;>|<cell|moveFrame>>|<row|<cell|>|<cell|;>|<cell|<around*|\<llangle\>|t|\<rrangle\>>>>|<row|<cell|>|<cell|;>|<cell|dropFrame>>|<row|<cell|<around*|\<llangle\>|<math-ss|unit><rsub|A>|\<rrangle\>>>|<cell|\<assign\>>|<cell|nop>>|<row|<cell|<around*|\<llangle\>|<math-ss|injl><rsub|A,B,C>
    t|\<rrangle\>>>|<cell|\<assign\>>|<cell|write<around*|(|0|)>;skip<around*|(|padL<around*|(|B,C|)>|)>;<around*|\<llangle\>|t|\<rrangle\>>>>|<row|<cell|<around*|\<llangle\>|<math-ss|injr><rsub|A,B,C>
    t|\<rrangle\>>>|<cell|\<assign\>>|<cell|write<around*|(|1|)>;skip<around*|(|padR<around*|(|B,C|)>|)>;<around*|\<llangle\>|t|\<rrangle\>>>>|<row|<cell|<around*|\<llangle\>|<math-ss|case><rsub|A,B,C,D>
    s t|\<rrangle\>>>|<cell|\<assign\>>|<cell|<around*|(|1+padL<around*|(|A,B|)>|)>\<star\><around*|\<llangle\>|s|\<rrangle\>>>>|<row|<cell|>|<cell|\|\|>|<cell|<around*|(|1+padR<around*|(|A,B|)>|)>\<star\><around*|\<llangle\>|t|\<rrangle\>>>>|<row|<cell|<around*|\<llangle\>|<math-ss|pair><rsub|A,B,C>
    s t|\<rrangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llangle\>|s|\<rrangle\>>;<around*|\<llangle\>|t|\<rrangle\>>>>|<row|<cell|<around*|\<llangle\>|<math-ss|take><rsub|A,B,C>
    t|\<rrangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llangle\>|t|\<rrangle\>>>>|<row|<cell|<around*|\<llangle\>|<math-ss|drop><rsub|A,B,C>
    t|\<rrangle\>>>|<cell|\<assign\>>|<cell|bitSize<around*|(|A|)>\<star\><around*|\<llangle\>|t|\<rrangle\>>>>>>
  </eqnarray*>

  <\theorem>
    Given a well-typed core Simplicity program <math|t:A\<vdash\>B> and an
    input <math|a:A>, then

    <\equation*>
      <prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>+m>\<vartriangleleft\>\<Xi\>|]>|<around*|\<llangle\>|t|\<rrangle\>>|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\><rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>
    </equation*>

    for any cell arrays <math|r<rsub|0>>, <math|r<rsub|0><rprime|'>>,
    <math|w<rsub|0>>, any stacks <math|\<Theta\>>, <math|\<Xi\>>, and any
    natural number <math|m>.
  </theorem>

  In particular, for a well-typed core Simplicity program
  <math|t:A\<vdash\>B>, we have

  <\equation*>
    <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<around*|\<llangle\>|t|\<rrangle\>>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>
  </equation*>

  which means we if we start the Bit Machine with only the input represented
  on the read stack, and enough space for the output on the write stack, the
  Bit Machine will compute the representation of the value
  <math|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>> without
  crashing.

  <subsubsection|Tail Composition Optimisation (TCO)>

  <assign|TCOon|<macro|x|<math|<around*|\<llangle\>|<arg|x>|\<rrangle\>><rsup|TCO><rsub|on>>>><assign|TCOoff|<macro|x|<math|<around*|\<llangle\>|<arg|x>|\<rrangle\>><rsup|TCO><rsub|off>>>>Traditional
  imperative language implementations often make use of tail call
  optimization that occurs when the last command of a procedure is a call to
  a second procedure. Normally the first procedure's stack frame would be
  free after the second procedure returns. The tail call optimization instead
  frees the first procedure's stack frame prior to the call to the second
  procedure instead. This can reduce the overall memory use of the program.

  The composition combinator, <math|<math-ss|comp>>, in Simplicity plays a
  role similar to a procedure call. We can perform a tail composition
  optimization that moves the <math|dropFrame> instruction earlier to reduce
  the overall memory requirements needed to evaluate Simplicity programs. We
  define an alternate translation of Simplicity programs to Bit Machine
  programs via two mutually recursively defined functions,
  <math|<TCOoff|\<cdummy\>>> and <TCOon|\<cdummy\>>:

  \;

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|15|28|2|2|cell-halign|r>|<table|<row|<cell|<TCOoff|<math-ss|iden><rsub|A>>>|<cell|\<assign\>>|<cell|copy<around*|(|bitSize<around*|(|A|)>|)>>>|<row|<cell|<TCOoff|<math-ss|comp><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|newFrame<around*|(|bitSize<around*|(|B|)>|)>>>|<row|<cell|>|<cell|;>|<cell|<TCOoff|s>>>|<row|<cell|>|<cell|;>|<cell|moveFrame>>|<row|<cell|>|<cell|;>|<cell|<TCOon|t>>>|<row|<cell|<TCOoff|<math-ss|unit><rsub|A>>>|<cell|\<assign\>>|<cell|nop>>|<row|<cell|<TCOoff|<math-ss|injl><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|write<around*|(|0|)>;skip<around*|(|padL<around*|(|B,C|)>|)>;<TCOoff|t>>>|<row|<cell|<TCOoff|<math-ss|injr><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|write<around*|(|1|)>;skip<around*|(|padR<around*|(|B,C|)>|)>;<TCOoff|t>>>|<row|<cell|<TCOoff|<math-ss|case><rsub|A,B,C,D>
    s t>>|<cell|\<assign\>>|<cell|<around*|(|1+padL<around*|(|A,B|)>|)>\<star\><TCOoff|s>>>|<row|<cell|>|<cell|\|\|>|<cell|<around*|(|1+padR<around*|(|A,B|)>|)>\<star\><TCOoff|t>>>|<row|<cell|<TCOoff|<math-ss|pair><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|<TCOoff|s>;<TCOoff|t>>>|<row|<cell|<TCOoff|<math-ss|take><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|<TCOoff|t>>>|<row|<cell|<TCOoff|<math-ss|drop><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|bitSize<around*|(|A|)>\<star\><TCOoff|t>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<TCOon|<math-ss|iden><rsub|A>>>|<cell|\<assign\>>|<cell|copy<around*|(|bitSize<around*|(|A|)>|)>>>|<row|<cell|>|<cell|;>|<cell|dropFrame>>|<row|<cell|<TCOon|<math-ss|comp><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|newFrame<around*|(|bitSize<around*|(|B|)>|)>>>|<row|<cell|>|<cell|;>|<cell|<TCOon|s>>>|<row|<cell|>|<cell|;>|<cell|moveFrame>>|<row|<cell|>|<cell|;>|<cell|<TCOon|t>>>|<row|<cell|<TCOon|<math-ss|unit><rsub|A>>>|<cell|\<assign\>>|<cell|dropFrame>>|<row|<cell|<TCOon|<math-ss|injl><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|write<around*|(|0|)>;skip<around*|(|padL<around*|(|B,C|)>|)>;<TCOon|t>>>|<row|<cell|<TCOon|<math-ss|injr><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|write<around*|(|1|)>;skip<around*|(|padR<around*|(|B,C|)>|)>;<TCOon|t>>>|<row|<cell|<TCOon|<math-ss|case><rsub|A,B,C,D>
    s t>>|<cell|\<assign\>>|<cell|fwd<around*|(|1+padL<around*|(|A,B|)>|)>;<TCOon|s>>>|<row|<cell|>|<cell|\|\|>|<cell|fwd<around*|(|1+padR<around*|(|A,B|)>|)>;<TCOon|t>>>|<row|<cell|<TCOon|<math-ss|pair><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|<TCOoff|s>;<TCOon|t>>>|<row|<cell|<TCOon|<math-ss|take><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|<TCOon|t>>>|<row|<cell|<TCOon|<math-ss|drop><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|fwd<around*|(|bitSize<around*|(|A|)>|)>;<TCOon|t>>>>>
  </eqnarray*>

  The definition of the <math|<TCOoff|\<cdummy\>>> translation is very
  similar to the naive one, except the <math|dropFrame> instruction at the
  end of the translation of the composition combinator is replaced by having
  a recursive call to <math|<TCOon|\<cdummy\>>> instead. The definition of
  <math|<TCOon|\<cdummy\>>> puts the <math|dropFrame> instruction in the
  translations of <math|<math-ss|iden>> and <math|<math-ss|unit>>. The
  <math|bwd> instructions are removed from the translations of
  <math|<math-ss|case>> and <math|<math-ss|drop>>. Lastly notice that the
  first recursive call in the translation of <math|<math-ss|pair>> is to
  <TCOoff|\<cdummy\>>.

  <\theorem>
    Given a well-typed core Simplicity program <math|t:A\<vdash\>B> and an
    input <math|a:A>, then

    <\equation*>
      <prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>+m>\<vartriangleleft\>\<Xi\>|]>|<TCOoff|t>|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\><rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>
    </equation*>

    and

    <\equation*>
      <prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\<vartriangleright\>r<rsub|0><emptyFrame><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>+m>\<vartriangleleft\>\<Xi\>|]>|<TCOon|t>|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\|w<rsub|0>\<cdummy\><rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>
    </equation*>

    for any cell arrays <math|r<rsub|0>>, <math|r<rsub|0><rprime|'>>,
    <math|w<rsub|0>>, any frame <math|r<rsub|1>>, any stacks
    <math|\<Theta\>>, <math|\<Xi\>>, and any natural number <math|m>.
  </theorem>

  In particular, for a well-typed core Simplicity program
  <math|t:A\<vdash\>B>, we have

  <\equation*>
    <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>
  </equation*>

  <section|Static Analysis>

  Static analysis lets us quickly compute properties of expressions, without
  the need for exhaustively executing expressions on all possible inputs. We
  use static analysis in Simplicity to bound the computation costs in terms
  of time and space of Simplicity expressions for all their inputs. The
  analysis we do are linear in the size of the DAG representing the
  Simplicity expression, and typically the analysis runs much faster than the
  cost of evaluating an expression on a single input. We can do this because
  the intermediate results of static analysis can be shared where there are
  shared sub-expressions.

  <subsection|Space Resources>

  The primary source of memory resources used by the Bit Machine is the cells
  used by all the frames that make of the state of Bit Machine. A secondary
  source of memory resources used comes from the overhead of the frames
  themselves, which need to store their boundaries or sizes, and the position
  of their cursors. In our analysis we will make a simplifying assumption
  that these boundaries / sizes / positions values are all of constant size.
  This assumption holds when the Bit Machine is implemented on real hardware
  which has an upper bound on its addressable memory and there is a limit on
  the number of Cells that can be held anyways.

  To bound these resources we perform a static analysis to compute an upper
  bound on the maximum number of cells needed when executing a Simplicity
  program on the Bit Machine for any input, and we compute an upper bound on
  the maximum number of frames needed as well.

  <subsubsection|Maximum Cell Count Bound>

  We define the cell count of a frame to be the length of its underlying cell
  array and the cell count of a Bit Machine state to be the sum of the cell
  counts of all its frames.

  <\eqnarray*>
    <tformat|<table|<row|<cell|cellCount<around*|(|<carr|c<rsub|1>*\<cdots\><wide*|c<rsub|i>|\<bar\>>\<cdots\>*c<rsub|n>>|)>>|<cell|\<assign\>>|<cell|n>>|<row|<cell|cellCount<around*|(|<around*|[|r<rsub|n>\<vartriangleright\>\<ldots\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<ldots\>\<vartriangleleft\>w<rsub|m>|]>|)>>|<cell|\<assign\>>|<cell|<big|sum><rsup|n><rsub|i=0>cellCount<around*|(|r<rsub|i>|)>+<big|sum><rsup|m><rsub|j=0>cellCount<around*|(|w<rsub|j>|)>>>|<row|<cell|cellCount<around*|(|<halted>|)>>|<cell|\<assign\>>|<cell|0>>>>
  </eqnarray*>

  We define the cells required by a program <prog|S<rsub|0>|p|S<rsub|1>> as
  the maximum cell count over every intermediate state.

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<cwith|1|1|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-col-span|2>|<table|<row|<cell|<math|cellsReq<around*|(|<prog|S|nop|S>|)>\<assign\>cellCount<around*|(|S|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<math|i:S<rsub|0>\<rightsquigarrow\>S<rsub|1>>>>|<row|<cell|<math|cellsReq<around*|(|<prog|S<rsub|0>|i|S<rsub|1>>|)>\<assign\>max<around*|(|cellCount<around*|(|S<rsub|0>|)>,cellCount<around*|(|S<rsub|1>|)>|)>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<prog|S<rsub|0>|k<rsub|0>|S<rsub|1>>>|<cell|<prog|S<rsub|1>|k<rsub|1>|S<rsub|2>>>>>>>>>|<row|<cell|<math|cellsReq<around*|(|<prog|S<rsub|0>|k<rsub|0>;k<rsub|1>|S<rsub|2>>|)>\<assign\>max<around*|(|cellsReq<around*|(|<prog|S<rsub|0>|k<rsub|0>|S<rsub|1>>|)>,cellsReq<around*|(|<prog|S<rsub|1>|k<rsub|1>|S<rsub|2>>|)>|)>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|0|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0>|S>>>|<row|<cell|<math|cellsReq<around*|(|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><carr|<wide*|0|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0><around*|\|||\|>*k<rsub|1>|S>|)>\<assign\>cellsReq<around*|(|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><carr|<wide*|0|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0>|S>|)>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|2|2|1|1|cell-col-span|2>|<table|<row|<cell|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><rsub|><carr|<wide*|1|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|1>|S>>>|<row|<cell|<math|cellsReq<around*|(|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><carr|<wide*|1|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|0><around*|\|||\|>*k<rsub|1>|S>|)>\<assign\>cellsReq<around*|(|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><carr|<wide*|1|\<bar\>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|k<rsub|1>|S>|)>>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<cwith|1|1|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-col-span|2>|<table|<row|<cell|<math|cellsReq<around*|(|<prog|<halted>|k|<halted>>|)>\<assign\>0>>>>>>
  </with>

  \;

  Note that when executing a Simplicity expression on the Bit Machine, the
  size of the state prior and after execution is identical. For naive
  translation of Simplicity to the Bit Machine, we can write a simple
  recursive function that bounds the number of additional Cells needed to
  evaluate a Simplicity expression beyond the size of the initial and final
  state.

  <\eqnarray*>
    <tformat|<cwith|2|10|2|2|cell-halign|r>|<cwith|2|10|2|2|cell-halign|r>|<table|<row|<cell|extraCellsBound<around*|(|<math-ss|iden><rsub|A>|)>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|extraCellsBound<around*|(|<math-ss|comp><rsub|A,B,C>
    s t|)>>|<cell|\<assign\>>|<cell|bitSize<around*|(|B|)>+max<around*|(|extraCellsBound<around*|(|s|)>,extraCellsBound<around*|(|t|)>|)>>>|<row|<cell|extraCellsBound<around*|(|<math-ss|unit><rsub|A>|)>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|extraCellsBound<around*|(|<math-ss|injl><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<around*|(|t|)>>>|<row|<cell|extraCellsBound<around*|(|<math-ss|injr><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<around*|(|t|)>>>|<row|<cell|extraCellsBound<around*|(|<math-ss|case><rsub|A,B,C,D>
    s t|)>>|<cell|\<assign\>>|<cell|max<around*|(|extraCellsBound<around*|(|s|)>,extraCellsBound<around*|(|t|)>|)>>>|<row|<cell|extraCellsBound<around*|(|<math-ss|pair><rsub|A,B,C>
    s t|)>>|<cell|\<assign\>>|<cell|max<around*|(|extraCellsBound<around*|(|s|)>,extraCellsBound<around*|(|t|)>|)>>>|<row|<cell|extraCellsBound<around*|(|<math-ss|take><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<around*|(|t|)>>>|<row|<cell|extraCellsBound<around*|(|<math-ss|drop><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<around*|(|t|)>>>>>
  </eqnarray*>

  <\lemma>
    For any core Simplicity expression <math|t:A\<vdash\>B>, such that

    <\equation*>
      <prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|<around*|\<llangle\>|t|\<rrangle\>>|<around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>
    </equation*>

    we have that

    <\enumerate>
      <item><math|cellCount<around*|(|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|)>=cellCount<around*|(|<around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>|)>>

      <item><math|cellsReq<around*|(|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|<around*|\<llangle\>|t|\<rrangle\>>|<around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>|)>\<leq\><next-line><htab|5mm>cellCount<around*|(|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|)>+extraCellsBound<around*|(|t|)>>.
    </enumerate>

    In particular for <math|a:A> and

    <\equation*>
      <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<around*|\<llangle\>|t|\<rrangle\>>|><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>
    </equation*>

    we have that

    <math|cellsReq<around*|(|<prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<around*|\<llangle\>|t|\<rrangle\>>|><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>|)>\<leq\><next-line><htab|5mm>bitSize<around*|(|A|)>+bitSize<around*|(|B|)>+extraCellsBound<around*|(|t|)>>.
  </lemma>

  We can compute a tighter bound for TCO translation, but the calculation is
  a bit more complicated. The number of extra cells needed depends on whether
  TCO is in the ``on'' state, and what the size of the active read frame is.

  <\eqnarray*>
    <tformat|<cwith|2|10|2|2|cell-halign|r>|<cwith|2|10|2|2|cell-halign|r>|<table|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|iden><rsub|A>|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|comp><rsub|A,B,C>
    s t|)>*<around*|(|r|)>>|<cell|\<assign\>>|<cell|bitSize<around*|(|B|)>+max<around*|(|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|s|)><around*|(|r|)>,<next-line>extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|bitSize<around*|(|B|)>|)>-r|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|unit><rsub|A>|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|0>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|injl><rsub|A,B,C>
    t|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|injr><rsub|A,B,C>
    t|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|case><rsub|A,B,C,D>
    s t|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|max<around*|(|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|s|)><around*|(|r|)>,<next-line>extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|r|)>|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|pair><rsub|A,B,C>
    s t|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|max<around*|(|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|s|)><rsup|\<nosymbol\>><around*|(|0|)>,<next-line>extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|r|)>|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|take><rsub|A,B,C>
    t|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|drop><rsub|A,B,C>
    t|)><around*|(|r|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>>>>>
  </eqnarray*>

  <\lemma>
    For any core Simplicity expression <math|t:A\<vdash\>B>, such that

    <\equation*>
      <prog|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|<TCOon|t>|<around*|[|\<Theta\><rsub|on><rprime|'>\<vartriangleright\>r<rsub|on,0><rprime|'>\|w<rsub|on,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|on><rprime|'>|]>><rsup|\<nosymbol\>>
    </equation*>

    and

    <\equation*>
      <prog|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|<TCOoff|t><rsup|\<nosymbol\>>|<around*|[|\<Theta\><rsub|off><rprime|'>\<vartriangleright\>r<rsub|off,0><rprime|'>\|w<rsub|off,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|off><rprime|'>|]>>
    </equation*>

    we have that

    <\enumerate>
      <item><math|cellCount<around*|(|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|)>=cellCount<around*|(|r<rsub|on,0>|)>+cellCount<around*|(|<around*|[|\<Theta\><rsub|on><rprime|'>\<vartriangleright\>r<rsub|on,0><rprime|'>\|w<rsub|on,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|on><rprime|'>|]>|)>>
      and<next-line><math|cellCount<around*|(|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|)>=cellCount<around*|(|<around*|[|\<Theta\><rsub|off><rprime|'>\<vartriangleright\>r<rsub|off,0><rprime|'>\|w<rsub|off,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|off><rprime|'>|]>|)>>

      <item><math|cellsReq<around*|(|<prog|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|<TCOon|t>|<around*|[|\<Theta\><rsub|on><rprime|'>\<vartriangleright\>r<rsub|on,0><rprime|'>\|w<rsub|on,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|on><rprime|'>|]>>|)>\<leq\><next-line><htab|5mm>cellCount<around*|(|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|)>+extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|cellCount<around*|(|r<rsub|on,0>|)>|)>>
      and<next-line><math|cellsReq<around*|(|<prog|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|<TCOoff|t><rsup|\<nosymbol\>>|<around*|[|\<Theta\><rsub|off><rprime|'>\<vartriangleright\>r<rsub|off,0><rprime|'>\|w<rsub|off,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|off><rprime|'>|]>>|)>\<leq\><next-line><htab|5mm>cellCount<around*|(|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|)>+extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|0|)>>.
    </enumerate>

    In particular for <math|a:A> and

    <\equation*>
      <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>
    </equation*>

    we have that

    <math|cellsReq<around*|(|<prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>|)>\<leq\><next-line><htab|5mm>bitSize<around*|(|A|)>+bitSize<around*|(|B|)>+extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|0|)>>.
  </lemma>

  The problem with <math|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>>
  is that it is effectively a dynamic analysis because its result is a
  function. We cannot directly use this definition to perform a static
  analysis because we cannot cache and reuse results on shared
  sub-expressions. Fortunately, we can characterize the set of possible
  functions returned by <math|extraCellsBound<rsup|TCO><rsub|dyn>> by a pair
  of parameters.

  <\equation*>
    interp<rsup|TCO><around*|\<langle\>|n,m|\<rangle\>><around*|(|r|)>\<assign\>max<around*|(|n-r,m|)>
  </equation*>

  We can write a static analysis to compute the pair of parameters that
  characterize the results of <math|extraCellsBound<rsup|TCO><rsub|dyn>>.

  <\eqnarray*>
    <tformat|<cwith|2|17|2|2|cell-halign|r>|<cwith|2|17|2|2|cell-halign|r>|<cwith|1|-1|2|2|cell-halign|c>|<cwith|10|10|2|2|cell-halign|r>|<cwith|11|11|2|2|cell-halign|r>|<cwith|13|14|2|2|cell-halign|r>|<cwith|13|14|2|2|cell-halign|r>|<cwith|13|14|2|2|cell-halign|c>|<cwith|13|13|2|2|cell-halign|r>|<cwith|14|14|2|2|cell-halign|r>|<cwith|3|4|2|2|cell-halign|r>|<cwith|3|4|2|2|cell-halign|r>|<cwith|3|4|2|2|cell-halign|c>|<cwith|3|4|2|2|cell-halign|r>|<cwith|3|4|2|2|cell-halign|r>|<cwith|3|4|2|2|cell-halign|c>|<cwith|3|3|2|2|cell-halign|r>|<cwith|4|4|2|2|cell-halign|r>|<cwith|5|5|2|2|cell-halign|r>|<table|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|iden><rsub|A>|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|0,0|\<rangle\>>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|comp><rsub|A,B,C>
    s t|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|max<around*|(|r<rsub|b>+n<rsub|s>,n<rsub|t>,r<rsub|b>+m<rsub|t>|)>,r<rsub|b>+m<rsub|s>|\<rangle\>>>>|<row|<cell|>|<cell|where>|<cell|<around*|\<langle\>|n<rsub|s>,m<rsub|s>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|s|)>>>|<row|<cell|>|<cell|and>|<cell|<around*|\<langle\>|n<rsub|t>,m<rsub|t>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>|<row|<cell|>|<cell|and>|<cell|r<rsub|b>\<assign\>bitSize<around*|(|B|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|unit><rsub|A>|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|0,0|\<rangle\>>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|injl><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|injr><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|case><rsub|A,B,C,D>
    s t|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|max<around*|(|n<rsub|s>,n<rsub|t>|)>,max<around*|(|m<rsub|s>,m<rsub|t>|)>|\<rangle\>>>>|<row|<cell|>|<cell|where>|<cell|<around*|\<langle\>|n<rsub|s>,m<rsub|s>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|s|)>>>|<row|<cell|>|<cell|and>|<cell|<around*|\<langle\>|n<rsub|t>,m<rsub|t>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|pair><rsub|A,B,C>
    s t|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|n<rsub|t>,max<around*|(|n<rsub|s>,m<rsub|s>,m<rsub|t>|)>|\<rangle\>>>>|<row|<cell|>|<cell|where>|<cell|<around*|\<langle\>|n<rsub|s>,m<rsub|s>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|s|)>>>|<row|<cell|>|<cell|and>|<cell|<around*|\<langle\>|n<rsub|t>,m<rsub|t>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|take><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|drop><rsub|A,B,C>
    t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>>>
  </eqnarray*>

  When computing <math|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>
  resulting values for shared sub-expressions can be shared, making
  <math|extraCellsBound<rsup|TCO><rsub|static>> a static analysis. We can use
  <math|interp<rsup|TCO>> and <math|extraCellsBound<rsup|TCO><rsub|static>>
  to compute <math|extraCellsBound<rsup|TCO><rsub|dyn>> for our bound on cell
  count.

  <\lemma>
    <math|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>=interp<rsup|TCO><around*|(|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>|)>>.
  </lemma>

  <\corollary>
    For any core Simplicity expression <math|t:A\<vdash\>B> and <math|a:A>
    such that

    <\equation*>
      <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>
    </equation*>

    we have that

    <math|cellsReq<around*|(|<prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>|)>\<leq\>bitSize<around*|(|A|)>+bitSize<around*|(|B|)>+max<around*|(|n,m|)>>

    <no-indent>where <math|<around*|\<langle\>|n,m|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>.
  </corollary>

  <subsubsection|Maximum Frame Count Bound>

  <subsection|Time Resources>

  <section|Commitment Merkle Root><label|ss:cmr>

  <assign|SimplicityPrefix|53696d706c69636974792d4472616674>In modern
  Bitcoin, users who use P2SH (pay to script hash) do not commit funds
  directly to Bitcoin Script, rather they commit to a hash of their Bitcoin
  Script. Only when they wish to redeem their funds do they reveal their
  Bitcoin Script for execution. Bitcoin's consensus protocol enforces that
  the Bitcoin Script presented during redemption has a hash that matches the
  committed hash.

  <assign|cmr|<macro|x|<math|#<rsup|c><around*|(|<arg|x>|)>>>><assign|imr0|<macro|x|<math|#<rsup|i><around*|(|<arg|x>|)>>>><assign|mr|<macro|x|y|<math|#<rsup|><rsup|<arg|x>><around*|(|<arg|y>|)>>>>Simplicity
  is designed to work in the same way. However, instead of a linear hash of a
  serialized Simplicity program (Section<nbsp><reference|ss:Serialization>)
  we follow the tree structure of a Simplicity expression and compute a
  commitment Merkle root of its syntax tree. Below we define both the
  commitment Merkle root of a Simplicity expression <math|t\<of\>A\<vdash\>B>
  as <math|<cmr|t>\<of\><2><rsup|256>> as well as a value
  <math|<imr0|t>\<of\><2><rsup|256>> that will later be used to define a
  varianted for identity Merkle Roots (Section<nbsp><reference|ss:IMR>).
  \ Below <math|\<alpha\>\<in\><around*|{|c,i|}>> and hence for core
  Simplicity expression <math|t>, <math|<cmr|t>=<imr0|t>>, but they will no
  longer be equal when we consider some extensions to core Simplicity.

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<mr|\<alpha\>|<math-ss|iden><rsub|A>>>|<cell|\<assign\>>|<cell|SHA256<rsup|tag<rsup|c><rsub|<math-ss|iden>>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|comp><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|<math|tag<rsup|c><rsub|<math-ss|comp>>>><rsub|IV>\<comma\>
    <around*|\<langle\>|<mr|\<alpha\>|s>,<mr|\<alpha\>|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<mr|\<alpha\>|<math-ss|unit><rsub|A>>>|<cell|\<assign\>>|<cell|SHA256<rsup|tag<rsup|c><rsub|<math-ss|unit>>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|injl><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|injl>>><rsub|IV>\<comma\>
    <around*|\<langle\>|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>,<mr|\<alpha\>|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<mr|\<alpha\>|<math-ss|injr><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|injr>>><rsub|IV>\<comma\>
    <around*|\<langle\>|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>,<mr|\<alpha\>|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<mr|\<alpha\>|<math-ss|case><rsub|A,B,C,D>
    s t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|case>>><rsub|IV>\<comma\>
    <around*|\<langle\>|<mr|\<alpha\>|s>,<mr|\<alpha\>|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<mr|\<alpha\>|<math-ss|pair><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|pair>>><rsub|IV>\<comma\>
    <around*|\<langle\>|<mr|\<alpha\>|s>,<mr|\<alpha\>|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<mr|\<alpha\>|<math-ss|take><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|take>>><rsub|IV>\<comma\>
    <around*|\<langle\>|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>,<mr|\<alpha\>|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<mr|\<alpha\>|<math-ss|drop><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|drop>>><rsub|IV>\<comma\>
    <around*|\<langle\>|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>,<mr|\<alpha\>|t>|\<rangle\>>|\<rangle\>>>>>>
  </eqnarray*>

  Here we are directly using SHA-256's compression function,
  <math|SHA256*<rsub|Block><around*|\<langle\>|i,b|\<rangle\>>>, which takes
  two arguments. The first argument, <math|i>, is a 256-bit tagged initial
  value. The second value, <math|b>, is a 512-bit block of data. Above we
  divide a block into two 256-bit values,
  <math|<around*|\<langle\>|b<rsub|0>,b<rsub|1>|\<rangle\>>>, and recursively
  pass Merkle roots into the compression function.

  Like static analysis, the time needed to computing the commitment Merkle
  root is linear in the size of the DAG representing the term because the
  intermediate results on sub-expressions can be shared.

  We define unique tags <math|tag<rsup|c><rsub|x>> for every combinator.

  <\eqnarray*>
    <tformat|<table|<row|<cell|tag<rsup|c><rsub|<math-ss|iden>>>|<cell|\<assign\>>|<cell|<math-tt|[<SimplicityPrefix>1f436f6d6d69746d656e741f6964656e]><rsub|2<rsup|8>>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|comp>>>|<cell|\<assign\>>|<cell|<math-tt|[<SimplicityPrefix>1f436f6d6d69746d656e741f636f6d70]><rsub|2<rsup|8>>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|unit>>>|<cell|\<assign\>>|<cell|<math-tt|[<SimplicityPrefix>1f436f6d6d69746d656e741f756e6974]><rsub|2<rsup|8>>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|injl>>>|<cell|\<assign\>>|<math-tt|[<SimplicityPrefix>1f436f6d6d69746d656e741f696e6a6c]><rsub|2<rsup|8>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|injr>>>|<cell|\<assign\>>|<math-tt|[<SimplicityPrefix>1f436f6d6d69746d656e741f696e6a72]><rsub|2<rsup|8>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|case>>>|<cell|\<assign\>>|<math-tt|[<SimplicityPrefix>1f436f6d6d69746d656e741f63617365]><rsub|2<rsup|8>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|pair>>>|<cell|\<assign\>>|<math-tt|[<SimplicityPrefix>1f436f6d6d69746d656e741f70616972]><rsub|2<rsup|8>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|take>>>|<cell|\<assign\>>|<math-tt|[<SimplicityPrefix>1f436f6d6d69746d656e741f74616b65]><rsub|2<rsup|8>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|drop>>>|<cell|\<assign\>>|<math-tt|[<SimplicityPrefix>1f436f6d6d69746d656e741f64726f70]><rsub|2<rsup|8>>>>>
  </eqnarray*>

  Notice that the type annotations for expressions are not included in the
  commitment Merkle root. We will rely on type inference to derive principle
  type annotations (see Section<nbsp><with|color|red|<reference|ss:typeInference>>).
  Later, we will make use of this flexibility when pruning unused branches
  from <samp|case> expressions (see Section<nbsp><reference|ss:pruning>).

  <section|Type Merkle Root>

  <assign|tmr|<macro|x|<math|#<rsup|ty><around*|(|<arg|x>|)>>>>We also define
  a Merkle root that follows the tree sturcture of types in the same way that
  we defined the commitment Merkle Root.

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<tmr|<1>>>|<cell|\<assign\>>|<cell|SHA256<rsup|tag<rsup|ty><rsub|<math-ss|one>>><rsub|IV>>>|<row|<cell|<tmr|A+B>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|<math|tag<rsup|ty><rsub|<math-ss|sum>>>><rsub|IV>\<comma\>
    <around*|\<langle\>|<tmr|A>,<tmr|B>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<tmr|A\<times\>B>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|<math|tag<rsup|ty><rsub|<math-ss|prod>>>><rsub|IV>\<comma\>
    <around*|\<langle\>|<tmr|A>,<tmr|B>|\<rangle\>>|\<rangle\>>>>>>
  </eqnarray*>

  We define unique tags <math|tag<rsup|ty><rsub|x>> for every sort of type.

  <\eqnarray*>
    <tformat|<table|<row|<cell|tag<rsup|ty><rsub|<math-ss|one>>>|<cell|\<assign\>>|<cell|<math-tt|[<SimplicityPrefix>1f547970651f756e6974]><rsub|2<rsup|8>>>>|<row|<cell|tag<rsup|ty><rsub|<math-ss|sum>>>|<cell|\<assign\>>|<cell|<math-tt|[<SimplicityPrefix>1f547970651f73756d]><rsub|2<rsup|8>>>>|<row|<cell|tag<rsup|ty><rsub|<math-ss|prod>>>|<cell|\<assign\>>|<cell|<math-tt|[<SimplicityPrefix>1f547970651f70726f64]><rsub|2<rsup|8>>>>>>
  </eqnarray*>

  <chapter|Simplicity Extensions>

  The core Simplicity completeness theorem
  (Theorem<nbsp><reference|thm:CSCT>) proves that the core Simplicity
  language is already computationally complete for Simplicity types. Our
  primary method of extending Simplicity is by adding expressions with
  side-effects. We will use monads to formally specify these new effects.

  <section|Monadic Semantics><label|ss:monadicSemantics>

  \;

  We define a new interpretation of Simplicity expressions,
  <math|t\<of\>A\<vdash\>B>, whose denotations are Kleisli morphisms,
  <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>>\<of\>A\<rightarrow\>\<cal-M\>*B>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|iden><rsub|A>|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|\<cal-M\>><around*|(|a|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|comp><rsub|A,B,C>
    s t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|<around*|(|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><op|\<leftarrowtail\>><around*|\<llbracket\>|s|\<rrbracket\>><rsup|\<cal-M\>>|)><around*|(|a|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|unit><rsub|A>|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|\<cal-M\>><around*|\<langle\>||\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|injl><rsub|A,B,C>
    t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<cal-M\><injl|<around*|(|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>|)>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|injr><rsub|A,B,C>
    t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<cal-M\><injr|<around*|(|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>|)>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|case><rsub|A,B,C,D>
    s t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injl|<around*|(|a|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|s|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a,c|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|case><rsub|A,B,C,D>
    s t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injr|<around*|(|b|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|b,c|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|pair><rsub|A,B,C>
    s t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<phi\><rsup|\<cal-M\>><around*|\<langle\>|<around*|\<llbracket\>|s|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>,<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|take><rsub|A,B,C>
    t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a,b|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|drop><rsub|A,B,C>
    t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a,b|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|b|)>>>>>
  </eqnarray*>

  The above interpretation for Kleisli morphisms is nearly uniquely defined
  (under the requirement of parametericity). Many well-typed variations of
  the definition above end up being equivalent due to the monad laws. The
  main choice we have is between using <math|\<phi\><rsup|\<cal-M\>><rsub|A,B>>
  or <math|<wide|\<phi\>|\<bar\>><rsup|\<cal-M\>><rsub|A,B>> in the
  definition of <math|<around*|\<llbracket\>|<math-ss|pair> s
  t|\<rrbracket\>><rsup|\<cal-M\>>>. The only other definitions amount to
  duplicating the effects of sub-expressions.

  To ensure that all these possible choices are immaterial, we demand that
  <math|\<cal-M\>> be a commutative, idempotent monad when interpreting
  Simplicity expressions. This lets us ignore the order of effects, and
  duplication of effects, which simplifies reasoning about Simplicity
  programs. It also provides an opportunity for a Simplicity optimizer to,
  for example, reorder pairs without worrying about changing the denotational
  semantics.

  <\theorem>
    For any core Simplicity expression, <math|t\<of\>A\<vdash\>B>, we have
    <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>>\<assign\>\<eta\><rsup|\<cal-M\>><rsub|B>\<circ\><around*|\<llbracket\>|t|\<rrbracket\>>>.
  </theorem>

  <\corollary>
    For any core Simplicity expression, <math|t\<of\>A\<vdash\>B>, we have
    <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|Id>\<assign\><around*|\<llbracket\>|t|\<rrbracket\>>>.
  </corollary>

  Notice that our monadic semantics are strict in their side-effects in the
  sense that the definition of <math|<around*|\<llbracket\>|<math-ss|pair> s
  t|\<rrbracket\>><rsup|\<cal-M\>>> implies that the side-effects of
  <math|<around*|\<llbracket\>|s|\<rrbracket\>><rsup|\<cal-M\>>> and
  <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>>> are both
  realized even if it ends up that one (or both) of the values returned by
  <math|s> and <math|t> end up never used.

  <section|Witness>

  Our first extension to core Simplicity is the witness expression. The
  language that uses this extension is called <dfn|Simplicity with
  witnesses>.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|b\<of\>B>>>|<row|<cell|<math|<math-ss|witness><rsub|A,B>
    b\<of\>A\<vdash\>B>>>>>>
  </with>

  \;

  The denotational semantics of the witness expression is simply a constant
  function that returns its parameter.

  \;

  <\equation*>
    <around*|\<llbracket\>|<math-ss|witness><rsub|A,B>
    b|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>\<assign\>\<eta\><rsup|\<cal-M\>><rsub|B><around*|(|b|)>
  </equation*>

  As far as semantics goes, this extension does not provide any new
  expressivity. A constant function for any value <math|b> can already be
  expressed in core Simplicity using <math|<samp|scribe><rsub|A,B><around*|(|b|)>>.
  The difference between <samp|scribe> and <samp|witness> expressions lies in
  their commitment Merkle root.

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|1|2|2|cell-halign|r>|<table|<row|<cell|<cmr|<math-ss|witness><rsub|A,B>
    b>>|<cell|\<assign\>>|<cell|SHA256<rsup|tag<rsup|c><rsub|<math-ss|witness>>><rsub|IV>>>>>
  </eqnarray*>

  where <math|tag<rsup|c><rsub|<math-ss|witness>>> value is a unique value.

  <\eqnarray*>
    <tformat|<table|<row|<cell|tag<rsup|c><rsub|<math-ss|witness>>>|<cell|\<assign\>>|<cell|<math-tt|[<SimplicityPrefix>1f436f6d6d69746d656e741f7769746e657373]><rsub|<2><rsup|8>>>>>>
  </eqnarray*>

  Notice that a <math|<samp|witness> b> expression does not commit to its
  parameter in the commitment root. This means that at redemption time a
  <samp|witness> expression's parameter, called a <dfn|witness value>, could
  be set to any value. This differs from the identity root
  (Section<nbsp><reference|ss:IMR>) which will include a commitment to its
  parameter.

  Witness values play the same role as Bitcoin Script's input stack in its
  <verbatim|sigScript> or Segwit's <verbatim|witness>. They act as inputs to
  Simplicity programs. Rather than accepting arguments as inputs and passing
  them down to where they are needed, <samp|witness> expressions lets input
  data appear right where it is needed.

  <subsection|Elided Computation>

  <subsection|Type Inference with Witness>

  Like other expressions, a <samp|witness> expression does not commit to its
  type in its commitment Merkle root. Type inference is used to compute the
  minimal type needed for each witness expression (see
  Section<nbsp><reference|ss:typeInference>) This helps ensures that third
  parties cannot perform witness malleation to add unused data on
  transactions during transit.

  <section|Assertions and Failure>

  Our first side-effect will be aborting a computation. New assertion and
  <samp|fail> expressions make use of this effect. The language that uses
  this extension is called <dfn|Simplicity with assertions>.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s\<of\>A\<times\>C\<vdash\>D>>|<cell|<math|h\<of\><2><rsup|256>>>>>>>>>|<row|<cell|<math|<math-ss|assertl><rsub|A,B,C,D>
    s h\<of\><around*|(|A+B|)>\<times\>C\<vdash\>D>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|h\<of\><2><rsup|256>>>|<cell|<math|t\<of\>B\<times\>C\<vdash\>D>>>>>>>>|<row|<cell|<math|<math-ss|assertr><rsub|A,B,C,D>
    h t\<of\><around*|(|A+B|)>\<times\>C\<vdash\>D>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|h\<of\><2><rsup|512>>>>|<row|<cell|<math|<math-ss|fail><rsub|A,B>
    h\<of\>A\<vdash\>B>>>>>>
  </with>

  \;

  Assertions serve a dual purpose. One purpose is to replicate the behaviour
  of Bitcoin Script's <verbatim|OP_VERIFY> and similar operations that are
  used to validate checks on programmable conditions, such as verifying that
  a digital signature verification passes or causing the program to abort
  otherwise.

  The second purpose is to support pruning of unused <samp|case> branches
  during redemption. The 256-bit value is used in the commitment Merkle root
  computation to hold Merkle root of the pruned branches. This will be
  covered in Section<nbsp><reference|ss:pruning>.

  Because we are extending Simplicity's semantics to support an abort effect,
  there is no harm in adding a generic <samp|fail> expression. The parameter
  to the <samp|fail> expression is used to support salted expressions (see
  Section<nbsp><reference|ss:salted>). We will see that <samp|fail>
  expressions never manifest themselves within a blockchain's consensus
  protocol.

  <subsection|Denotational Semantics>

  Given an commutative, idempotent monad with zero, <math|\<cal-M\>>, we
  extend the monadic semantics for Simplicity expressions,
  <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>>>, to include
  assertion expressions:

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|assertl><rsub|A,B,C,D>
    s h|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injl|<around*|(|a|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|s|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a,c|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|assertl><rsub|A,B,C,D>
    s h|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injr|<around*|(|b|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|\<cal-M\>><rsub|D>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|assertr><rsub|A,B,C,D>
    h t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injl|<around*|(|a|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|\<cal-M\>><rsub|D>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|assertr><rsub|A,B,C,D>
    h t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injr|<around*|(|b|)>>,c|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|b,c|\<rangle\>>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|fail><rsub|A,B>
    h|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|\<cal-M\>><rsub|B>>>>>
  </eqnarray*>

  Notice that the <math|h> parameters are ignored in the semantics. They will
  be used instead for the Merkle root definitions in
  Section<nbsp><reference|ss:AssertMerkleRoot>.

  A term in the language of core Simplicity extended with witnesses and
  assertions, <math|t\<of\>A\<vdash\>B>, can be interpreted as a function
  returning an optional result: <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|<maybe>>\<of\>A\<rightarrow\><maybe>B>,
  using the option monad (see Section<nbsp><reference|ss:optionMonad>).

  <\theorem>
    For any core Simplicity expression with assertions,
    <math|t\<of\>A\<vdash\>B>, and any commutative idempotent monad with zero
    <math|\<cal-M\>>, we have <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>>\<assign\>\<iota\><rsup|\<cal-M\>><rsub|<maybe>,B>\<circ\><around*|\<llbracket\>|t|\<rrbracket\>><rsup|<maybe>>>.
  </theorem>

  <subsection|Merkle Roots><label|ss:AssertMerkleRoot>

  We extend the definition of commitment Merkle root and identity Merkle root
  to support the new assertion and <samp|fail> expressions

  \;

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|1|2|2|cell-halign|r>|<table|<row|<cell|<mr|\<alpha\>|<math-ss|assertl><rsub|A,B,C,D>
    s h>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|case>>><rsub|IV>\<comma\>
    <around*|\<langle\>|<mr|\<alpha\>|s>,h|\<rangle\>>|\<rangle\>>>>|<row|<cell|<mr|\<alpha\>|<math-ss|assertr><rsub|A,B,C,D>
    h t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|case>>><rsub|IV>\<comma\>
    <around*|\<langle\>|h,<mr|\<alpha\>|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<mr|\<alpha\>|<math-ss|fail><rsub|A,B>
    h>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|fail>>><rsub|IV>,h|\<rangle\>>>>>>
  </eqnarray*>

  where <math|tag<rsup|c><rsub|<math-ss|fail>>> value is a unique value.

  <\eqnarray*>
    <tformat|<table|<row|<cell|tag<rsup|c><rsub|<math-ss|fail>>>|<cell|\<assign\>>|<cell|<math-tt|[<SimplicityPrefix>1f436f6d6d69746d656e741f6661696c]><rsub|<2><rsup|8>>>>>>
  </eqnarray*>

  It is important to notice that we are reusing
  <math|tag<rsup|c><rsub|<math-ss|case>>> when tagging assertions in their
  commitment Merkle root. Also notice that the <math|h> value, which was
  ignored in the semantics, is used in the commitment Merkle root. Together
  this allows an assertion expression to substitute for a case expression at
  redemption time while maintaining the same commitment Merkle root. This
  enables a feature of Simplicity called pruning.

  \;

  <subsubsection|Pruning Unused <samp|case> Branches><label|ss:pruning>

  The commitment Merkle roots of the assertion expression reuses
  <math|tag<rsup|c><rsub|<math-ss|case>>> in the compression function. This
  means that the following identities hold.

  <\equation*>
    <cmr|<math-ss|assertl><rsub|A,B,C,D> s
    <cmr|t>>=<cmr|<math-ss|case><rsub|A,B,C,D> s
    t>=<cmr|<math-ss|assertr><rsub|A,B,C,D> <cmr|s> t>
  </equation*>

  In particular, it means that when a <math|<math-ss|case>> expression is
  used at commitment time, it can be replaced by an assertion expression. If
  we substitute a <samp|case> with an assertion expression and that assertion
  fails during evaluation, then the whole transaction will be deemed invalid
  and rejected. On the other hand if the assertion does not fail, then we are
  guaranteed to end up with the same result as before (which ultimately could
  still be failure due to a later assertion failure). Therefore, assuming the
  transaction is valid, a substitution of assertions will not change the
  semantics.

  We can take advantage of this by performing this substitution at redemption
  time. We can effectively replace any unused branch in a case expression
  with its commitment Merkle root. In fact, we will require this replacement
  to occur during redemption (see Section<nbsp><inactive|<reference|<with|color|red|TODO>>>).

  For those cases where we want to use an assertion at commitment time, for
  example when performing something similar to Bitcoin Script's
  <verbatim|OP_VERIFY>, we use the following derived <math-ss|assert>
  combinator,

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|t\<of\>A\<vdash\><2>>>>>>>>>|<row|<cell|<math|<math-ss|assert><rsub|A>
    t\<assign\>t \<vartriangle\> <math-ss|unit>;<math-ss|assertr>
    <cmr|<math-ss|fail> <around*|\<lfloor\>|0|\<rfloor\>><rsub|512>>
    <math-ss|unit>\<of\>A\<vdash\><1>>>>>>>
  </with>

  \;

  <no-indent>where <math|<around*|\<lfloor\>|0|\<rfloor\>><rsub|512>> is used
  as a canonical parameter for <samp|fail>. Naturally, the
  <around*|\<lfloor\>|0|\<rfloor\>><rsub|512> parameter can be replaced with
  any value. This can be used as a method of salting expression, which is the
  subject of the next section.

  <\theorem>
    For any core Simplicity expression <math|t\<of\>A\<vdash\><2>>,

    <\equation*>
      <around*|\<llbracket\>|<math-ss|assert><rsub|A>
      t|\<rrbracket\>><rsup|S>=<around*|\<llbracket\>|t|\<rrbracket\>><text|.>
    </equation*>
  </theorem>

  <subsubsection|Salted Expressions><label|ss:salted>

  During pruning, unused branches are replaced by its commitment Merkle root.
  Since hashes are one way functions, one might believe that third parties
  will be unable to recover the pruned branch from just its commitment Merkle
  root. However, this argument is not so straightforward. Whether or not the
  expression can be recovered from just its commitment Merkle root depends on
  how much entropy the pruned expression contains. Third parties can grind,
  testing many different expressions, until they find one whose commitment
  Merkle root matches the one occurring in the assertion. If the entropy of
  the pruned expression is low, then this grinding is feasible.

  Some expressions naturally have high entropy. For example, any branch that
  contains a commitment to a public key will have at least the entropy of the
  public key space. However, this only holds so long as that public key is
  not reused nor will ever be reused elsewhere.

  For expressions that reuse public keys, or otherwise naturally having low
  entropy, one can add salt, which is random data, to increase its entropy.
  There are several possible ways to incorporate random data into a
  Simplicity expression without altering the program's semantics. One way is
  to incorporate the <samp|fail> expression which lets us directly
  incorporate random into is commitment Merkle root.

  Given a block of random data, <math|h:<2><rsup|512>>, and a Simplicity
  expression <math|t\<of\>A\<vdash\>B>, we can define two salted variants of
  <math|t>:

  <\eqnarray*>
    <tformat|<table|<row|<cell|<math-ss|salted><rsup|0> h
    t>|<cell|\<assign\>>|<cell|<math-ss|witness>
    <math-tt|0><rsub|<2>><math-ss|> \<vartriangle\>
    <math-ss|iden>;<math-ss|assertl> <around*|(|<math-ss|drop> t|)>
    <cmr|<math-ss|fail> h>:A\<vdash\>B>>|<row|<cell|<math-ss|salted><rsup|1>
    h t>|<cell|\<assign\>>|<cell|<math-ss|witness>
    <math|<math-tt|1><rsub|<2>>> \<vartriangle\>
    <math-ss|iden>;<math-ss|assertr> <cmr|<math-ss|fail> h>
    <around*|(|<math-ss|drop> t|)>:A\<vdash\>B>>>>
  </eqnarray*>

  The <math|<math-ss|salted><rsup|b> h t> expression will have high entropy
  so long as the random data <math|h> has high entropy. By randomly choosing
  between these two variants, this method of salting obscures the fact that
  the expression is salted at all. Without knowing <math|h>, it is
  impractical to determine if <math|#<rsup|c><around*|(|<math-ss|fail> h|)>>
  is the commitment Merkle root of a <samp|fail> expression, or if it is a
  some other, high-entropy, alternate expression that the redeemer has simply
  chosen not to execute.

  By explicitly using the <samp|fail> expression here, one has the option
  prove that these alternative branches are unexecutable by revealing the
  value <math|h>. If the Simplicity expression is part of a multi-party smart
  contract, it maybe required to reveal <math|h> (or prove in a deniable way
  that such an <math|h> exists) to all party members so everyone can vet the
  security properties of the overall smart contract.

  Of course, lots of variations of this <samp|salted> expression are
  possible.

  <section|Blockchain Primitives>

  We extend Simplicity with primitive expressions that provide blockchain
  specific features. Naturally the specifics of these primitive expressions
  depends on the specific blockchain application, but generally speaking the
  primitives allow reading data from the context that a Simplicity program is
  being executed within. This is usually the data of the encompassing
  transaction including details about the inputs and outputs of the
  transaction, and which specific input is being evaluated.

  A blockchain application needs to provide a set of typed primitive
  expressions and a monad to capture the side-effects for these primitives.
  This monad should be a commutative, idempotent monad with zero in order to
  interpret Simplicity and its extensions. All primitive expressions must be
  monomorphic and have no parameters (i.e. they are not themselves
  combinators).

  In the next section we will be detailing the primitives used for Bitcoin,
  or a Bitcoin-like application. In Appendix<nbsp><reference|app:ElementsTransactions>
  we describe the primitives used for the Elements sidechain.

  <subsection|Bitcoin Transactions><label|ss:BitcoinTransactions>

  For the Bitcoin application, Simplicity's primitives will be primarily
  focuses on accessing the <dfn|signed transaction data>, which is the data
  that is hashed and signed in Bitcoin.

  We define a record type that captures this environment, called
  <math|BCEnv>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|Lock>|<cell|\<assign\>>|<cell|<2><rsup|32>>>|<row|<cell|Value>|<cell|\<assign\>>|<cell|<2><rsup|64>>>|<row|<cell|Outpoint>|<cell|\<assign\>>|<cell|<2><rsup|256>\<times\><2><rsup|32>>>|<row|<cell|SigInput>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|prevOutpoint\<of\>Outpoint>>|<row|<cell|value\<of\>Value<with|color|red|<text|make
    this SigOutput?>>>>|<row|<cell|sequence\<of\><2><rsup|32>>>>>>|}>>>|<row|<cell|SigOutput>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|value\<of\>Value>>|<row|<cell|pubScript\<of\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>>>>>>|}>>>|<row|<cell|SigTx>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|version\<of\><2><rsup|32>>>|<row|<cell|inputs\<of\>SigInput<rsup|+>>>|<row|<cell|outputs\<of\>SigOutput<rsup|+>>>|<row|<cell|lockTime\<of\>Lock>>>>>|}>>>|<row|<cell|BCEnv>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|tx\<of\>SigTx>>|<row|<cell|ix\<of\><2><rsup|32>>>|<row|<cell|scriptCMR\<of\><2><rsup|256>>>>>>|}>>>>>
  </eqnarray*>

  The type <math|SigTx> contains the signed transaction data. Following a
  design similar to BIP 143, this signed transaction data excludes
  transaction inputs' ScriptSigs and includes inputs' Bitcoin values. The
  <math|ix> field is input index whose redemption is being processed by this
  Simplicity program. The <math|scriptCMR> field holds the commitment Merkle
  root of the Simplicity program being executed.

  The <math|SigTx> type given above allows for an unbounded number of inputs
  and outputs. However, there are limits imposed by the Bitcoin protocol. The
  number of inputs and outputs are limited to less than or equal to
  <math|2<rsup|25>> by Bitcoin's deserialization implementation. Similarly,
  the length of <math|SigOutput>'s <math|pubScript> is limited to less than
  or equal to <math|2<rsup|25>> bytes. We assume all transactions to adhere
  to these limits when reasoning about Bitcoin transactions.

  Furthermore, we assume that for every <math|e\<of\>BCEnv> that
  <math|<around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>\<less\><around*|\||e<around*|[|tx|]><around*|[|inputs|]>|\|>>
  so that ``current'' index being validated is, in fact, an input of the
  transaction.

  Bitcoin's money supply is capped below <math|21<nbsp>000<nbsp>000\<times\>10<rsup|8>>
  satoshi, therefore it is safe to assume that all monetary values are within
  this bound. In particular, we assume that for every <math|e\<of\>BCEnv>
  that the following inequalities hold.

  <\equation*>
    0\<leq\>fold<rsup|<around*|\<langle\>|+,0|\<rangle\>>><rsub|\<bbb-N\>><around*|(|<around*|(|\<lambda\>o\<point\><around*|\<lceil\>|o<around*|[|value|]>|\<rceil\>><rsub|64>|)><rsup|+><around*|(|e<around*|[|tx|]><around*|[|outputs|]>|)>|)>\<leq\>fold<rsup|<around*|\<langle\>|+,0|\<rangle\>>><rsub|\<bbb-N\>><around*|(|<around*|(|\<lambda\>i\<point\><around*|\<lceil\>|i<around*|[|value|]>|\<rceil\>><rsub|64>|)><rsup|+><around*|(|e<around*|[|tx|]><around*|[|inputs|]>|)>|)>\<leq\>21<nbsp>000<nbsp>000\<times\>10<rsup|8>
  </equation*>

  \;

  <assign|BC|<math|BC>>The monad we use for the Bitcoin application provides
  an environment effect (also known as a reader effect) that allows
  read-access to the <math|BCEnv> value defining the Simplicity program's
  evaluation context. We call this monad <math|BC>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<BC>A>|<cell|\<assign\>>|<cell|BCEnv\<rightarrow\><maybe>A>>|<row|<cell|<BC>f<around*|(|a|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\><maybe>f<around*|(|a<around*|(|e|)>|)>>>>>
  </eqnarray*>

  \;

  <BC> is a commutative, idempotent monad with zero:

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<eta\><rsup|<BC>><rsub|A><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><rsub|A><around*|(|a|)>>>|<row|<cell|\<mu\><rsup|<BC>><rsub|A><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<mu\><rsup|<maybe>><rsub|A><around*|(|<maybe><around*|(|\<lambda\>f\<point\>f<around*|(|e|)>|)><around*|(|a<around*|(|e|)>|)>|)>>>|<row|<cell|\<emptyset\><rsup|<BC>><rsub|A>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<emptyset\><rsup|<maybe>><rsub|A>>>>>
  </eqnarray*>

  \;

  We define several new primitive expressions for reading data from a
  <math|BCEnv> value. The language that uses this extension is called
  <dfn|Simplicity with Bitcoin>.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|version>\<of\><value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|lockTime>\<of\><value|1>\<vdash\>Lock>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputsHash>\<of\><value|1>\<vdash\><2><rsup|256>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|outputsHash>\<of\><value|1>\<vdash\><2><rsup|256>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|numInputs>\<of\><value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|totalInputValue>\<of\><value|1>\<vdash\>Value>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentPrevOutpoint>\<of\><value|1>\<vdash\>OutPoint>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentValue>\<of\><value|1>\<vdash\>Value>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentSequence>\<of\><value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentIndex>\<of\><value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputPrevOutpoint>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|Outpoint|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputValue>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|Value|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputSequence>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<2><rsup|32>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|numOutputs>\<of\><value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|totalOutputValue>\<of\><value|1>\<vdash\>Value>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|outputValue>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|Value|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|outputScriptHash>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<2><rsup|256>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|scriptCMR>\<of\><value|1>\<vdash\><2><rsup|256>>>>>>>
  </with>

  <subsubsection|Denotational Semantics><label|ss:BTDenotationalSemantics>

  We extend the formal semantics of these new expressions as follows.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|version>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|e<around*|[|tx|]><around*|[|version|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|lockTime>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|e<around*|[|tx|]><around*|[|lockTime|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputsHash>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\><around*|(|\<eta\><rsup|<maybe>>\<circ\>SHA256\<circ\>\<mu\><rsup|\<ast\>>\<circ\>\<eta\><rsup|S>\<circ\>inputHash<rsup|+>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|outputsHash>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\><around*|(|\<eta\><rsup|<maybe>>\<circ\>SHA256\<circ\>\<mu\><rsup|\<ast\>>\<circ\>\<eta\><rsup|S>\<circ\>outputHash<rsup|+>|)><around*|(|e<around*|[|tx|]><around*|[|outputs|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|numInputs>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|\<lfloor\>|<around*|\||e<around*|[|tx|]><around*|[|inputs|]>|\|>|\<rfloor\>><rsub|32>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|totalInputValue>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|fold<rsup|<around*|\<lfloor\>|+|\<rfloor\>><rsub|64>><around*|(|<around*|(|\<lambda\>l\<point\>l<around*|[|value|]>|)><rsup|+><around*|(|e<around*|[|tx|]><around*|[|inputs|]>|)>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentPrevOutpoint>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\><maybe><around*|(|\<lambda\>l\<point\>l<around*|[|prevOutpoint|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentValue>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\><maybe><around*|(|\<lambda\>l\<point\>l<around*|[|value|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentSequence>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\><maybe><around*|(|\<lambda\>l\<point\>l<around*|[|sequence|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentIndex>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|e<around*|[|ix|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputPrevOutpoint>>|\<rrbracket\>><rsup|<BC>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|prevOutpoint|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputValue>>|\<rrbracket\>><rsup|<BC>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|value|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputSequence>>|\<rrbracket\>><rsup|<BC>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|sequence|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|numOutputs>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|\<lfloor\>|<around*|\||e<around*|[|tx|]><around*|[|outputs|]>|\|>|\<rfloor\>><rsub|32>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|totalOutputValue>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|fold<rsup|<around*|\<lfloor\>|+|\<rfloor\>><rsub|64>><around*|(|<around*|(|\<lambda\>l\<point\>l<around*|[|value|]>|)><rsup|+><around*|(|e<around*|[|tx|]><around*|[|outputs|]>|)>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|outputValue>>|\<rrbracket\>><rsup|<BC>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|value|]>|)><around*|(|e<around*|[|tx|]><around*|[|outputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|outputScriptHash>>|\<rrbracket\>><rsup|<BC>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>SHA256<around*|(|l<around*|[|pubScript|]>|)>|)><around*|(|e<around*|[|tx|]><around*|[|outputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|scriptCMR>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>BCEnv\<point\>\<eta\><rsup|<maybe>><around*|(|e<around*|[|scriptCMR|]>|)>>>>>
  </eqnarray*>

  where

  <\eqnarray*>
    <tformat|<table|<row|<cell|inputHash<around*|(|l|)>>|<cell|\<assign\>>|<cell|BE<rsub|256><around*|(|\<pi\><rsub|1><around*|(|l<around*|[|prevOutpoint|]>|)>|)>\<cdummy\>LE<rsub|32><around*|(|\<pi\><rsub|2><around*|(|l<around*|[|prevOutpoint|]>|)>|)>\<cdummy\>LE<rsub|64><around*|(|l<around*|[|value|]>|)>\<cdummy\>LE<rsub|32><around*|(|l<around*|[|sequence|]>|)>>>|<row|<cell|ouputHash<around*|(|l|)>>|<cell|\<assign\>>|<cell|LE<rsub|64><around*|(|l<around*|[|value|]>|)>\<cdummy\>BE<rsub|256><around*|(|SHA256<around*|(|l<around*|[|pubScript|]>|)>|)>>>>>
  </eqnarray*>

  <with|color|red|Consider making everything big endian?>

  For most of these primitive expressions, it is clear that they can never
  fail, in the sense of never returning <math|\<emptyset\><rsup|<maybe>>>.
  The expressions <math|<around*|\<llbracket\>|<samp|currentPrevOutpoint>|\<rrbracket\>><rsup|BC>>,
  <math|<around*|\<llbracket\>|<samp|currentValue>|\<rrbracket\>><rsup|BC>>
  and <math|<around*|\<llbracket\>|<samp|currentSequence>|\<rrbracket\>><rsup|BC>>
  look like they could fail under some circumstances; however the assumption
  that for every <math|e\<of\>BCEnv> that
  <math|<around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>\<less\><around*|\||e<around*|[|tx|]><around*|[|inputs|]>|\|>>
  implies that those expressions cannot fail either.

  The sums computed for <math|<around*|\<llbracket\>|<math-ss|<math|totalInputValue>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>
  and <math|<around*|\<llbracket\>|<math-ss|<math|totalOutputValue>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>
  never ``overflow'' their 64-bit values due to our assumptions about
  Bitcoin's money supply.

  <subsubsection|Merkle Roots><label|ss:BTMerkleRoots>

  We extend the definition of the commitment Merkle root and identity Merkle
  root to support the new expressions by using the initial value of with tags
  of new unique byte strings.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<mr|\<alpha\>|<math-ss|version>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[76657273696f6e]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|lockTime>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[6c6f636b54696d65]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|inputsHash>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[696e7075747348617368]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|outputsHash>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[6f75747075747348617368]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|numInputs>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[6e756d496e70757473]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|totalInputValue>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[746f74616c496e70757456616c7565]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|currentPrevOutpoint>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[63757272656e74507265764f7574706f696e74]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|currentValue>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[63757272656e7456616c7565]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|currentSequence>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[63757272656e7453657175656e6365]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|currentIndex>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[63757272656e74496e646578]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|inputPrevOutpoint>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[696e707574507265764f7574706f696e74]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|inputValue>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[696e70757456616c7565]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|inputSequence>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[696e70757453657175656e6365]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|numOutput>s>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[6e756d784f757470757473]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|totalOutputValue>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[746f74616c4f757470757456616c7565]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|outputValue>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[6f757470757456616c7565]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|outputScriptHash>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[6f757470757453637269707448617368]>><rsub|IV>>>|<row|<cell|<mr|\<alpha\>|<math-ss|<math|scriptCMR>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|BCprefix\<cdummy\><math-tt|[736372697074434d52]>><rsub|IV>>>>>
  </eqnarray*>

  where

  <\equation*>
    BCprefix\<assign\><math-tt|[<SimplicityPrefix>1f5072696d69746976651f426974636f696e1f]>
  </equation*>

  <section|Simplicity Programs>

  Ultimately, we only are interested in the side-effects of Simplicity
  expressions; we only care that a particular expression does not fail when
  executed within the context of a given transaction. We do not care about
  the output value of a Simplicity expression, nor do we provide explicit
  inputs to Simplicity expressions, which are handled by <samp|witness>
  expressions instead.

  To this end, we define a <dfn|Simplicity program> to be a Simplicity
  expression of type <math|<1>\<vdash\><1>>. A core Simplicity expression of
  this type is useless. However, a Simplicity program with witnesses,
  assertions, and Bitcoin, <math|t\<of\><1>\<vdash\><1>>, has semantics of
  <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>\<of\>BCEnv
  \<rightarrow\> <2>>, which is the type of predicates over <math|BCEnv>.
  This is exactly what we want to use a Blockchain program for: to decide if
  a given set of witness data authorizes the redemption of funds for a
  specific input of a specific transaction. A particular input authorizes the
  transaction in the context <math|e\<of\>BCEnv> only when
  <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>><around*|(|e|)>=<math-tt|1><rsub|<2>>>,
  and all inputs must authorize the transaction for the transaction to be
  valid.

  Let us look at a basic example of a Simplicity program that requires a
  single Schnorr signature.

  <subsection|Example: <math-ss|checkSigHashAll>><label|ss:checkSigHashAll>

  Using Simplicity with witnesses, assertions and Bitcoin, we are able to
  build an expression that use Schnorr signatures to authorize spending of
  funds. Using the assertion extension we are able to define a variant of
  <math|<math-ss|bip0340-check>> called <math|<math-ss|bip0340-verify>>:

  <\equation*>
    <math-ss|bip0340-verify>\<assign\> <math-ss|assert>
    <math-ss|bip0340-check>\<of\><around*|(|PubKey\<times\>Msg|)>\<times\>Sig\<vdash\><1>
  </equation*>

  such that

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|bip0340-verify>|\<rrbracket\>><rsup|<maybe>><around*|\<langle\>|<around*|\<langle\>|p,m|\<rangle\>>,s|\<rangle\>>=\<eta\><rsup|<maybe>><around*|\<langle\>||\<rangle\>>>|<cell|\<Leftrightarrow\>>|<cell|<around*|\<llbracket\>|<math-ss|bip0340-check>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|p,m|\<rangle\>>,s|\<rangle\>>=<math-tt|1><rsub|<2>><text|.>>>>>
  </eqnarray*>

  Next, we use the Bitcoin transaction extension to build a
  <math|<math-ss|hashAll>> expression that computes a SHA-256 hash that
  commits to all of the current transaction data from the environment and
  which input is being signed for.

  <\render-code>
    <math|<math-ss|hashAll>\<of\><1>\<vdash\><2><rsup|256>>

    <math|<tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|5|5|2|2|cell-halign|r>|<cwith|6|6|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|hashAll>>>|<cell|:=>|<cell|(<math|<math-ss|scribe><around*|(|SHA256<rsub|IV><rsup|<math-tt|[<SimplicityPrefix>1f53696748617368]>>|)>>>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|<around*|(|<math|<math-ss|<math|inputsHash>>
    \<vartriangle\> <math-ss|<math|outputsHash>>>|)>>>|<row|<cell|>|<cell|;>|<cell|<math-ss|sha256-block>)>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|<math|<around*|(|<around*|(|<around*|(|<samp|currentValue>
    \<vartriangle\> <around*|(|<samp|currentIndex> \<vartriangle\>
    <math-ss|lockTime>|)>|)> |\<nobracket\>>|\<nobracket\>>>>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|<math|<around*|\<nobracket\>|
    <around*|\<nobracket\>| <around*|(|<around*|(|<math-ss|version>
    \<vartriangle\> <math-ss|scribe><around*|(|<around*|\<lfloor\>|2<rsup|31>|\<rfloor\>><rsub|32>|)>|)>
    \<vartriangle\> <math-ss|scribe><around*|(|<around*|\<lfloor\>|0|\<rfloor\>><rsub|64>|)>|)>|)>
    \<vartriangle\> <math-ss|scribe><around*|(|<around*|\<lfloor\>|1184|\<rfloor\>><rsub|256>|)>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math-ss|sha256-block>>>>>>>>>>>>
  </render-code>

  The <math-ss|hashAll> expression derives a total of 672 bits of data from
  the environment. The initial <math|SHA256> adds one 512-bit block constant
  prefix to this, which totals 1184 bits of data. While it is not strictly
  necessary, we choose to explicitly append the SHA-256 padding for this
  length of data.

  Next we pair the commitment Merkle root of <samp|hashAll> with its output.
  This commitment Merkle root plays the role of the signature hash flag that
  is covered by the signature in Bitcoin script. It is a specification of
  which parts of the transaction data is being signed, and exactly how those
  parts are combined to form the digest being signed.

  <\render-code>
    <math|<math-ss|sigHashAll>\<of\><1>\<vdash\><2><rsup|256>>

    <math|<tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|4|4|2|2|cell-halign|r>|<table|<row|<cell|<math-ss|sigHashAll>>|<cell|:=>|<cell|<math-ss|scribe><around*|(|SHA256<rsub|IV><rsup|<math-tt|[<SimplicityPrefix>1f5369676e6174757265]>>|)>>|<cell|>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|<around*|(|<samp|scribe><around*|(|<math|<cmr|<math-ss|hashAll>>>|)><math|\<vartriangle\>><samp|hashAll>|)>>|<cell|>>|<row|<cell|>|<cell|;>|<cell|<math-ss|sha256-block>)<math|\<vartriangle\>><math-ss|scribe><around*|(|<around*|\<lfloor\>|2<rsup|511>+1024|\<rfloor\>><rsub|512>|)>>|<cell|>>|<row|<cell|>|<cell|;>|<cell|<math-ss|sha256-block>>|<cell|>>>>>>>>>>>
  </render-code>

  The pair of the commitment Merkle root and the digest itself is 512 bits.
  \ The initial <math|SHA256> adds one 512-bit block constant prefix to this,
  which totals 1024 bits of data. While it is not strictly necessary, we
  choose to explicitly append the SHA-256 padding for this length of data.

  Finally, given a Schnorr public key <math|p\<of\>PubKey> and a Schnorr
  signature <math|s\<of\>Sig> we can create a Simplicity program that checks
  the signature against the public key and above message digest.

  <\render-code>
    <math|<math-ss|checkSigHashAll><around*|\<langle\>|p,s|\<rangle\>>\<of\><1>\<vdash\><1>>

    <math|<tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math-ss|checkSigHashAll><around*|\<langle\>|p,s|\<rangle\>>>|<cell|:=>|<cell|<around*|(|<math-ss|scribe><rsub|PubKey><around*|(|p|)><math-ss|<math|<math|>\<vartriangle\>><math|<math-ss|sigHashAll>>>|)>
    \<vartriangle\> <math-ss|witness><rsub|Sig><around*|(|s|)>>>|<row|<cell|>|<cell|;>|<cell|<math-ss|bip0340-verify>>>>>>>>>>>>
  </render-code>

  The <math-ss|witness> combinator ensures that the program's commitment
  Merkle root <math|<cmr|<math-ss|checkSigHashAll><around*|\<langle\>|p,s|\<rangle\>>>>
  is independent of the value of the signature <math|s>. This allows us to
  commit to this program without commiting to the signature, and only
  providing the signature at redemption time. As with normal Bitcoin
  transactions, the signature is only valid in the context,
  <math|e\<of\>BCEnv>, of a particular input on a particular transaction
  during redemption because our program only executes successfully, i.e.
  <math|<around*|\<llbracket\>|<math-ss|checkSigHashAll><around*|\<langle\>|p,s|\<rangle\>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>><around*|(|e|)>=\<eta\><rsup|<maybe>><around*|\<langle\>||\<rangle\>>>,
  when provided a witness that is a valid signature on the transaction data
  and index number.

  <section|Schnorr Signature Aggregation>

  <section|Malleability>

  <subsection|Transaction Weight>

  <chapter|Jets>

  <with|color|red|Reminder: build jets for parsing
  <math-ss|lockTime>s.><chapter|Delegation>

  Our last Simplicity extension is the <samp|disconnect> combinator. This
  extension allows for delegation but using it loses some nice properties of
  Simplicity. The language that uses this extension is called <dfn|Simplicity
  with delegation>. The language that uses this and all other extensions is
  called <dfn|full Simplicity with delegation>.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s\<of\><2><rsup|256>\<times\>A\<vdash\>B\<times\>C>>|<cell|<math|t\<of\>C\<vdash\>D>>>>>>>>|<row|<cell|<math|<math-ss|disconnect><rsub|A,B,C,D>
    s t\<of\>A\<vdash\>B\<times\>D>>>>>>
  </with>

  \;

  Semantically, the <samp|disconnect> combinator behaves similar to the
  composition combinator, but where the commitment Merkle root of the
  expression <math|t> is passed as an argument to the expression <math|s>. We
  extend our formal semantics to the <samp|disconnect> combinator by defining
  it in terms of core Simplicity as follows.

  <\equation*>
    <around*|\<llbracket\>|<math-ss|disconnect><rsub|A,B,C,D> s
    t|\<rrbracket\>><rsup|\<cal-M\>>\<assign\><around*|\<llbracket\>|<math-ss|scribe><rsub|A,<2><rsup|256>><around*|(|<cmr|t>|)>\<vartriangle\>
    <math|<math-ss|iden>>;s;<math-ss|take> <math-ss|iden> \<vartriangle\>
    <math-ss|drop> t|\<rrbracket\>><rsup|\<cal-M\>>
  </equation*>

  We can simplify the semantics as follows.

  <\equation*>
    <math|<around*|\<llbracket\>|<math-ss|disconnect><rsub|A,B,C,D> s
    t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>=<around*|(|<math|<around*|\<llbracket\>|<math-ss|take>
    <math-ss|iden> \<vartriangle\> <math-ss|drop>
    t|\<rrbracket\>><rsup|\<cal-M\>>>\<leftarrowtail\><around*|\<llbracket\>|s|\<rrbracket\>><rsup|\<cal-M\>>|)><around*|\<langle\>|<cmr|t>,a|\<rangle\>>>
  </equation*>

  Like a <samp|witness> expression, the real significance comes from the form
  of its commitment Merkle root. We extend the definition of the commitment
  Merkle root as follows.

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|1|2|2|cell-halign|r>|<table|<row|<cell|<cmr|<math-ss|disconnect><rsub|A,B,C,D>
    s t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|disconnect>>><rsub|IV>\<comma\>
    <around*|\<langle\>|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>,<cmr|s>|\<rangle\>>|\<rangle\>>>>>>
  </eqnarray*>

  where the <math|tag<rsup|c><rsub|<math-ss|disconnect>>> value is a unique
  value.

  <\small>
    <\eqnarray*>
      <tformat|<table|<row|<cell|tag<rsup|c><rsub|<math-ss|disconnect>>>|<cell|\<assign\>>|<cell|<math-tt|[<SimplicityPrefix>1f436f6d6d69746d656e741f646973636f6e6e656374]><rsub|<2><rsup|8>>>>>>
    </eqnarray*>
  </small>

  The commitment Merkle root only commits to the first argument, <math|s>, of
  a <math|<samp|disconnect> s t> expression. During redemption the second
  argument, <math|t>, can be freely set to any Simplicity expression. This
  differs from the identity root (Section<nbsp><reference|ss:IMR>) which will
  include a commitment to both arguments. In order to place restrictions on
  what <math|t> is allowed, the commitment Merkle root of <math|t> is passed
  to <math|s> as an input. This way <math|s> is allowed to dynamically decide
  if <math|t> is an acceptable expression to be used here.

  The primary purpose of <samp|disconnect> is for delegation. In this
  scenario, <math|s>, validates that the commitment Merkle root
  <math|<cmr|t>> is signed by a fixed public key. This lets a user postpone
  defining <math|t> until redemption time, while still maintaining full
  control, because any redemption requires their signature on <cmr|t>. For
  example, a user can require that <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>>>
  returns a public key. After commitment, but before redemption, the user can
  delegate authorization to redeem these funds to a third party by signing
  the that party's key in this fashion.

  The <samp|disconnect> combinator comes with some significant caveats.
  Because the whole program is not committed to at commitment time, it is no
  longer possible to statically analyze the maximum resource costs for
  redemption before commitment. During redemption
  <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>>> could, a
  priori, perform arbitrary amounts computation. Indeed we can use
  <samp|disconnect> to commit to what are effectively unbounded loops in
  Simplicity (see Section<nbsp><reference|ss:unboundedLoop>). Contrast this
  with the <samp|witness> expression, where type inference limits the size of
  the witness data, so bounds are still possible to compute.

  Of course, depending on the specifics of the policy enforced by <math|s>,
  it may be possible to bound the maximum resource costs for redemption in
  specific cases. However, that depends on the details of <math|s> and there
  is no practical, universal algorithm that will work for any Simplicity
  expression. Using <samp|disconnect> risks creating program that ends up
  impractical to redeem due to costs. This danger is why <samp|disconnect> is
  not part of full Simplicity and it is instead considered an extension to be
  used with caution.

  However, it is also important to note that static analysis can be performed
  at redemption time. At that point time the <math|t> expression has been
  provided and usual static analysis can proceed. Static analysis can still
  be part of the consensus protocol, even when the <samp|disconnect>
  expression is used.

  <section|Implementing <samp|disconnect> on the Bit Machine>

  The semantics of the <samp|disconnect> combinator can tell us how to
  implement it on the Bit Machine. \ We simply define the translation of the
  <samp|disconnect> combinator to be the translation of its semantics.

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|2|2|2|2|cell-halign|r>|<cwith|3|3|2|2|cell-halign|r>|<table|<row|<cell|<math|<around*|\<llangle\>|<math-ss|disconnect><rsub|A,B,C,D>
    s t|\<rrangle\>>>>|<cell|\<assign\>>|<cell|<around*|\<llangle\>|<math-ss|scribe><rsub|A,<2><rsup|256>><around*|(|<cmr|t>|)>\<vartriangle\>
    <math|<math-ss|iden>>;<around*|(|s;<math-ss|take> <math-ss|iden>
    \<vartriangle\> <math-ss|drop> t|)>|\<rrangle\>>>>|<row|<cell|<TCOoff|<math|<math-ss|disconnect><rsub|A,B,C,D>
    s t>>>|<cell|\<assign\>>|<cell|<TCOoff|<math-ss|scribe><rsub|A,<2><rsup|256>><around*|(|<cmr|t>|)>\<vartriangle\>
    <math|<math-ss|iden>>;<around*|(|s;<math-ss|take> <math-ss|iden>
    \<vartriangle\> <math-ss|drop> t|)>>>>|<row|<cell|<TCOon|<math|<math-ss|disconnect><rsub|A,B,C,D>
    s t>>>|<cell|\<assign\>>|<cell|<TCOon|<math-ss|scribe><rsub|A,<2><rsup|256>><around*|(|<cmr|t>|)>\<vartriangle\>
    <math|<math-ss|iden>>;<around*|(|s;<math-ss|take> <math-ss|iden>
    \<vartriangle\> <math-ss|drop> t|)>>>>>>
  </eqnarray*>

  We can expand out each of these definitions in turn to see their definition
  in terms of Bit Machine operations:

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|7|7|2|2|cell-halign|r>|<cwith|8|8|2|2|cell-halign|r>|<cwith|1|5|2|2|cell-halign|r>|<cwith|4|8|2|2|cell-halign|r>|<cwith|4|4|2|2|cell-halign|r>|<cwith|4|4|2|2|cell-halign|r>|<cwith|9|9|2|2|cell-halign|r>|<cwith|9|9|2|2|cell-halign|r>|<cwith|9|9|2|2|cell-halign|r>|<table|<row|<cell|<around*|\<llangle\>|<math-ss|disconnect><rsub|A,B,C,D>
    s t|\<rrangle\>>>|<cell|=>|<cell|newFrame<around*|(|256+bitSize<around*|(|A|)>|)>>>|<row|<cell|>|<cell|;>|<cell|write<rsub|<2><rsup|256>><around*|(|<cmr|t>|)>;copy<around*|(|bitSize<around*|(|A|)>|)>>>|<row|<cell|>|<cell|;>|<cell|moveFrame>>|<row|<cell|>|<cell|;>|<cell|newFrame<around*|(|bitSize<around*|(|B|)>+bitSize<around*|(|C|)>|)>>>|<row|<cell|>|<cell|;>|<cell|<around*|\<llangle\>|s|\<rrangle\>>>>|<row|<cell|>|<cell|;>|<cell|moveFrame>>|<row|<cell|>|<cell|;>|<cell|copy<around*|(|bitSize<around*|(|B|)>|)>;bitSize<around*|(|B|)>\<star\><around*|\<llangle\>|t|\<rrangle\>>>>|<row|<cell|>|<cell|;>|<cell|dropFrame>>|<row|<cell|>|<cell|;>|<cell|dropFrame>>>>
  </eqnarray*>

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|7|7|2|2|cell-halign|r>|<cwith|1|5|2|2|cell-halign|r>|<cwith|4|8|2|2|cell-halign|r>|<cwith|4|4|2|2|cell-halign|r>|<cwith|4|4|2|2|cell-halign|r>|<table|<row|<cell|<TCOoff|<math|<math-ss|disconnect><rsub|A,B,C,D>
    s t>>>|<cell|=>|<cell|newFrame<around*|(|256+bitSize<around*|(|A|)>|)>>>|<row|<cell|>|<cell|;>|<cell|write<rsub|<2><rsup|256>><around*|(|<cmr|t>|)>;copy<around*|(|bitSize<around*|(|A|)>|)>>>|<row|<cell|>|<cell|;>|<cell|moveFrame>>|<row|<cell|>|<cell|;>|<cell|newFrame<around*|(|bitSize<around*|(|B|)>+bitSize<around*|(|C|)>|)>>>|<row|<cell|>|<cell|;>|<cell|<TCOon|s>>>|<row|<cell|>|<cell|;>|<cell|moveFrame>>|<row|<cell|>|<cell|;>|<cell|copy<around*|(|bitSize<around*|(|B|)>|)>;fwd<around*|(|bitSize<around*|(|B|)>|)>;<TCOon|t>>>>>
  </eqnarray*>

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|8|8|2|2|cell-halign|r>|<cwith|1|6|2|2|cell-halign|r>|<cwith|5|9|2|2|cell-halign|r>|<cwith|5|5|2|2|cell-halign|r>|<cwith|5|5|2|2|cell-halign|r>|<table|<row|<cell|<TCOon|<math|<math-ss|disconnect><rsub|A,B,C,D>
    s t>>>|<cell|=>|<cell|newFrame<around*|(|256+bitSize<around*|(|A|)>|)>>>|<row|<cell|>|<cell|;>|<cell|write<rsub|<2><rsup|256>><around*|(|<cmr|t>|)>;copy<around*|(|bitSize<around*|(|A|)>|)>>>|<row|<cell|>|<cell|;>|<cell|dropFrame>>|<row|<cell|>|<cell|;>|<cell|moveFrame>>|<row|<cell|>|<cell|;>|<cell|newFrame<around*|(|bitSize<around*|(|B|)>+bitSize<around*|(|C|)>|)>>>|<row|<cell|>|<cell|;>|<cell|<TCOon|s>>>|<row|<cell|>|<cell|;>|<cell|moveFrame>>|<row|<cell|>|<cell|;>|<cell|copy<around*|(|bitSize<around*|(|B|)>|)>;fwd<around*|(|bitSize<around*|(|B|)>|)>;<TCOon|t>>>>>
  </eqnarray*>

  where

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|4|2|2|cell-halign|r>|<cwith|4|4|2|2|cell-halign|r>|<cwith|2|2|2|2|cell-halign|r>|<cwith|2|2|2|2|cell-halign|r>|<cwith|3|3|2|2|cell-halign|r>|<cwith|3|3|2|2|cell-halign|r>|<cwith|3|3|2|2|cell-halign|r>|<cwith|3|3|2|2|cell-halign|r>|<table|<row|<cell|write<rsub|<2><rsup|1>><around*|(|<math-tt|0><rsub|<2>>|)>>|<cell|\<assign\>>|<cell|write<around*|(|0|)>;skip<around*|(|0|)>;nop>>|<row|<cell|write<rsub|<2><rsup|1>><around*|(|<math-tt|1><rsub|<2>>|)>>|<cell|\<assign\>>|<cell|write<around*|(|1|)>;skip<around*|(|0|)>;nop>>|<row|<cell|write<rsub|<2><rsup|2n>><around*|(|<around*|\<langle\>|a,b|\<rangle\>>|)>>|<cell|\<assign\>>|<cell|write<rsub|<2><rsup|n>><around*|(|a|)>;write<rsub|<2><rsup|n>><around*|(|b|)>>>>>
  </eqnarray*>

  Of course, in an optimized implementation of <samp|disconnect> we would
  discard the <math|skip<around*|(|0|)>> and <math|nop> operations from the
  definition of <math|write<rsub|<2><rsup|256>>>. <with|color|red|TODO:
  before doing Time Resource static analysis we may need to formally define
  this optimized implemenation of <samp|disconnect>.>

  Because the Bit Machine instructions are directly derived from the
  semantics of <samp|disconnect> the correctness theorems for the Bit Machine
  still hold.

  <\theorem>
    Given a well-typed Simplicity program with delegation
    <math|t:A\<vdash\>B> and an input <math|a:A>, then

    <\equation*>
      <prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>+m>\<vartriangleleft\>\<Xi\>|]>|<around*|\<llangle\>|t|\<rrangle\>>|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\><rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>
    </equation*>

    for any cell arrays <math|r<rsub|0>>, <math|r<rsub|0><rprime|'>>,
    <math|w<rsub|0>>, any stacks <math|\<Theta\>>, <math|\<Xi\>>, and any
    natural number <math|m>.
  </theorem>

  In particular, for a well-typed Simplicity program with delegation
  <math|t:A\<vdash\>B>, we have

  <\equation*>
    <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<around*|\<llangle\>|t|\<rrangle\>>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>
  </equation*>

  <\theorem>
    Given a well-typed Simplicity program with delegation
    <math|t:A\<vdash\>B> and an input <math|a:A>, then

    <\equation*>
      <prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>+m>\<vartriangleleft\>\<Xi\>|]>|<TCOoff|t>|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0><emptyFrame><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\><rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>
    </equation*>

    and

    <\equation*>
      <prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\<vartriangleright\>r<rsub|0><emptyFrame><rep|a|>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0><emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>+m>\<vartriangleleft\>\<Xi\>|]>|<TCOon|t>|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|1>\|w<rsub|0>\<cdummy\><rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>
    </equation*>

    for any cell arrays <math|r<rsub|0>>, <math|r<rsub|0><rprime|'>>,
    <math|w<rsub|0>>, any frame <math|r<rsub|1>>, any stacks
    <math|\<Theta\>>, <math|\<Xi\>>, and any natural number <math|m>.
  </theorem>

  In particular, for a well-typed Simplicity program with delegation
  <math|t:A\<vdash\>B>, we have

  <\equation*>
    <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>
  </equation*>

  <subsection|Static Analysis of <samp|disconnect>>

  <subsubsection|Space Resources>

  Because the Bit Machine implementation of the <samp|disconnect> combinator
  is derived from its semantics in core Simplicity, we can derive the static
  analysis of the space resources used by the Bit Machine implementation of
  the <samp|disconnect> combintor from its definining Simplicity expression.

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|2|2|2|2|cell-halign|r>|<cwith|3|3|2|2|cell-halign|r>|<table|<row|<cell|extraCellsBound<around*|(|<math-ss|disconnect><rsub|A,B,C,D>
    s t|)><math|>>|<cell|\<assign\>>|<cell|extraCellsBound<next-line><htab|5mm><around*|(|<math-ss|scribe><rsub|A,<2><rsup|256>><around*|(|<cmr|t>|)>\<vartriangle\>
    <math|<math-ss|iden>>;<around*|(|s;<math-ss|take> <math-ss|iden>
    \<vartriangle\> <math-ss|drop> t|)>|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|disconnect><rsub|A,B,C,D>
    s t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|dyn><next-line><htab|5mm><around*|(|<math-ss|scribe><rsub|A,<2><rsup|256>><around*|(|<cmr|t>|)>\<vartriangle\>
    <math|<math-ss|iden>>;<around*|(|s;<math-ss|take> <math-ss|iden>
    \<vartriangle\> <math-ss|drop> t|)>|)>>>|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|disconnect><rsub|A,B,C,D>
    s t|)>>|<cell|\<assign\>>|<cell|extraCellsBound<rsup|TCO><rsub|static><next-line><htab|5mm><around*|(|<math-ss|scribe><rsub|A,<2><rsup|256>><around*|(|<cmr|t>|)>\<vartriangle\>
    <math|<math-ss|iden>>;<around*|(|s;<math-ss|take> <math-ss|iden>
    \<vartriangle\> <math-ss|drop> t|)>|)>>>>>
  </eqnarray*>

  We can expand out each of these definitions in turn:

  \;

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|3|2|2|cell-halign|r>|<cwith|2|4|2|2|cell-halign|r>|<cwith|2|2|2|2|cell-halign|r>|<cwith|2|2|2|2|cell-halign|r>|<table|<row|<cell|extraCellsBound<around*|(|<math-ss|disconnect><rsub|A,B,C,D>
    s t|)><math|>>|<cell|=>|<cell|256+bitSize<around*|(|A|)>>>|<row|<cell|>|<cell|+>|<cell|bitSize<around*|(|B|)>+bitSize<around*|(|C|)>>>|<row|<cell|>|<cell|+>|<cell|max<around*|(|extraCellsBound<around*|(|s|)>,extraCellsBound<around*|(|t|)>|)>>>>>
  </eqnarray*>

  \;

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|2|2|2|cell-halign|r>|<cwith|2|4|2|2|cell-halign|r>|<cwith|1|3|2|2|cell-halign|r>|<cwith|1|2|2|2|cell-halign|r>|<cwith|2|3|2|2|cell-halign|r>|<cwith|1|1|2|2|cell-halign|c>|<cwith|2|2|2|2|cell-halign|r>|<cwith|2|2|2|2|cell-halign|r>|<cwith|2|2|2|2|cell-halign|c>|<cwith|2|2|2|2|cell-halign|r>|<cwith|3|3|2|2|cell-halign|r>|<cwith|3|3|2|2|cell-halign|r>|<cwith|3|3|2|2|cell-halign|c>|<cwith|3|3|2|2|cell-halign|r>|<table|<row|<cell|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|<math-ss|disconnect><rsub|A,B,C,D>
    s t|)><around*|(|r|)>>|<cell|=>|<cell|max<around*|(|r<rsub|a>,
    max<around*|(|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|s|)><around*|(|r<rsub|a>|)>+r<rsub|a>,<next-line><htab|5mm>extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|r<rsub|b>|)>|)>+r<rsub|b>-r|)>>>|<row|<cell|>|<cell|where>|<cell|r<rsub|a>\<assign\>256+bitSize<around*|(|A|)>>>|<row|<cell|>|<cell|and>|<cell|r<rsub|b>\<assign\>bitSize<around*|(|B|)>+bitSize<around*|(|C|)>>>>>
  </eqnarray*>

  \;

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|3|2|2|cell-halign|r>|<cwith|2|6|2|2|cell-halign|r>|<cwith|2|2|2|2|cell-halign|r>|<cwith|2|2|2|2|cell-halign|r>|<cwith|2|3|2|2|cell-halign|r>|<cwith|2|3|2|2|cell-halign|r>|<cwith|2|3|2|2|cell-halign|c>|<cwith|2|2|2|2|cell-halign|r>|<cwith|3|3|2|2|cell-halign|r>|<cwith|1|1|2|2|cell-halign|c>|<cwith|4|4|2|2|cell-halign|r>|<cwith|4|4|2|2|cell-halign|r>|<cwith|4|4|2|2|cell-halign|c>|<cwith|4|4|2|2|cell-halign|r>|<cwith|5|5|2|2|cell-halign|r>|<cwith|5|5|2|2|cell-halign|r>|<cwith|5|5|2|2|cell-halign|c>|<cwith|5|5|2|2|cell-halign|r>|<table|<row|<cell|extraCellsBound<rsup|TCO><rsub|static><around*|(|<math-ss|disconnect><rsub|A,B,C,D>
    s t|)><math|>>|<cell|=>|<cell|<around*|\<langle\>|max<around*|(|n<rsub|t>,r<rsub|b>+max<around*|(|n<rsub|s>,m<rsub|t>,r<rsub|a>+m<rsub|s>|)>|)>,r<rsub|a>|\<rangle\>>>>|<row|<cell|>|<cell|where>|<cell|<around*|\<langle\>|n<rsub|s>,m<rsub|s>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|s|)>>>|<row|<cell|>|<cell|and>|<cell|<around*|\<langle\>|n<rsub|t>,m<rsub|t>|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>>|<row|<cell|>|<cell|and>|<cell|r<rsub|a>\<assign\>256+bitSize<around*|(|A|)>>>|<row|<cell|>|<cell|and>|<cell|r<rsub|b>\<assign\>bitSize<around*|(|B|)>+bitSize<around*|(|C|)>>>>>
  </eqnarray*>

  The correctness theorems about these analyses still holds:

  <\lemma>
    For any Simplicity expression with delegation <math|t:A\<vdash\>B>, such
    that

    <\equation*>
      <prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|<around*|\<llangle\>|t|\<rrangle\>>|<around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>
    </equation*>

    we have that

    <\enumerate>
      <item><math|cellCount<around*|(|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|)>=cellCount<around*|(|<around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>|)>>

      <item><math|cellsReq<around*|(|<prog|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|<around*|\<llangle\>|t|\<rrangle\>>|<around*|[|\<Theta\><rprime|'>\<vartriangleright\>r<rsub|0><rprime|'>\|w<rsub|0><rprime|'>\<vartriangleleft\>\<Xi\><rprime|'>|]>>|)>\<leq\><next-line><htab|5mm>cellCount<around*|(|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\|w<rsub|0>\<vartriangleleft\>\<Xi\>|]>|)>+extraCellsBound<around*|(|t|)>>.
    </enumerate>

    In particular for <math|a:A> and

    <\equation*>
      <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<around*|\<llangle\>|t|\<rrangle\>>|><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>
    </equation*>

    we have that

    <math|cellsReq<around*|(|<prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<around*|\<llangle\>|t|\<rrangle\>>|><around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>|)>\<leq\><next-line><htab|5mm>bitSize<around*|(|A|)>+bitSize<around*|(|B|)>+extraCellsBound<around*|(|t|)>>.
  </lemma>

  <\lemma>
    For any Simplicity expression with delegation <math|t:A\<vdash\>B>, such
    that

    <\equation*>
      <prog|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|<TCOon|t>|<around*|[|\<Theta\><rsub|on><rprime|'>\<vartriangleright\>r<rsub|on,0><rprime|'>\|w<rsub|on,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|on><rprime|'>|]>><rsup|\<nosymbol\>>
    </equation*>

    and

    <\equation*>
      <prog|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|<TCOoff|t><rsup|\<nosymbol\>>|<around*|[|\<Theta\><rsub|off><rprime|'>\<vartriangleright\>r<rsub|off,0><rprime|'>\|w<rsub|off,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|off><rprime|'>|]>>
    </equation*>

    we have that

    <\enumerate>
      <item><math|cellCount<around*|(|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|)>=cellCount<around*|(|r<rsub|on,0>|)>+cellCount<around*|(|<around*|[|\<Theta\><rsub|on><rprime|'>\<vartriangleright\>r<rsub|on,0><rprime|'>\|w<rsub|on,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|on><rprime|'>|]>|)>>
      and<next-line><math|cellCount<around*|(|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|)>=cellCount<around*|(|<around*|[|\<Theta\><rsub|off><rprime|'>\<vartriangleright\>r<rsub|off,0><rprime|'>\|w<rsub|off,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|off><rprime|'>|]>|)>>

      <item><math|cellsReq<around*|(|<prog|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|<TCOon|t>|<around*|[|\<Theta\><rsub|on><rprime|'>\<vartriangleright\>r<rsub|on,0><rprime|'>\|w<rsub|on,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|on><rprime|'>|]>>|)>\<leq\><next-line><htab|5mm>cellCount<around*|(|<around*|[|\<Theta\><rsub|on>\<vartriangleright\>r<rsub|on,0>\|w<rsub|on,0>\<vartriangleleft\>\<Xi\><rsub|on>|]>|)>+extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|cellCount<around*|(|r<rsub|on,0>|)>|)>>
      and<next-line><math|cellsReq<around*|(|<prog|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|<TCOoff|t><rsup|\<nosymbol\>>|<around*|[|\<Theta\><rsub|off><rprime|'>\<vartriangleright\>r<rsub|off,0><rprime|'>\|w<rsub|off,0><rprime|'>\<vartriangleleft\>\<Xi\><rsub|off><rprime|'>|]>>|)>\<leq\><next-line><htab|5mm>cellCount<around*|(|<around*|[|\<Theta\><rsub|off>\<vartriangleright\>r<rsub|off,0>\|w<rsub|off,0>\<vartriangleleft\>\<Xi\><rsub|off>|]>|)>+extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|0|)>>.
    </enumerate>

    In particular for <math|a:A> and

    <\equation*>
      <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>
    </equation*>

    we have that

    <math|cellsReq<around*|(|<prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>|)>\<leq\><next-line><htab|5mm>bitSize<around*|(|A|)>+bitSize<around*|(|B|)>+extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)><around*|(|0|)>>.
  </lemma>

  <\lemma>
    For any Simplicity expression with delegation <math|t:A\<vdash\>B>,

    <\equation*>
      <math|extraCellsBound<rsup|TCO><rsub|dyn><around*|(|t|)>=interp<rsup|TCO><around*|(|extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>|)>><text|.>
    </equation*>
  </lemma>

  <\corollary>
    For any Simplicity expression with delegation <math|t:A\<vdash\>B> and
    <math|a:A> such that

    <\equation*>
      <prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>
    </equation*>

    we have that

    <math|cellsReq<around*|(|<prog|<around*|[|<emptyFrame><rep|a|>\|<emptyFrame><carr|?><rsup|bitSize<around*|(|B|)>>|]>|<TCOoff|t>|<around*|[|<emptyFrame><rep|a|>\|<rep|<around*|\<llbracket\>|t|\<rrbracket\>><around*|(|a|)>|><emptyFrame>|]>>|)>\<leq\>bitSize<around*|(|A|)>+bitSize<around*|(|B|)>+max<around*|(|n,m|)>>

    <no-indent>where <math|<around*|\<langle\>|n,m|\<rangle\>>\<assign\>extraCellsBound<rsup|TCO><rsub|static><around*|(|t|)>>.
  </corollary>

  <section|Unbounded Loops><label|ss:unboundedLoop>

  While the primary purpose of <samp|disconnect> is for delegation, the
  construct can be used to create what is effectively an unbounded loop in
  Simplicity. Given a Simplicity expression, <math|t\<of\>A\<vdash\>A+B>, we
  can build a commitment Merkle root to an expression that will repeatedly
  recursively evaluate <math|<around*|\<llbracket\>|t|\<rrbracket\>>:A
  \<rightarrow\>A+B> on an input <math|A> until a <math|B> value is returned.

  Consider a Simplicity expression <math|t\<of\>A\<vdash\>A+B>, and a
  continuation <math|k\<of\>A\<times\><2><rsup|256>\<vdash\>B>. We define
  <math|<samp|loopBody> t k>:

  <\render-code>
    <math|<math-ss|loopBody> t k\<of\>A\<times\><2><rsup|256>\<vdash\>B>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|loopBody>
    t k>>|<cell|:=>|<cell|<math|<math-ss|take> t \<vartriangle\>
    <math-ss|IH>>>>|<row|<cell|>|<cell|;>|<cell|<samp|case>
    <math|<around*|(|<math-ss|disconnect> <around*|(|<math-ss|assert>
    <around*|(|<math-ss|IIH> \<vartriangle\> <math-ss|OH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\> <math-ss|IH>|)> k;
    <math|<math-ss|IH>>|)>> <math|<math-ss|OH>>>>>>>>>>>>
  </render-code>

  \;

  Let us consider the semantics <math|<around*|\<llbracket\>|<math-ss|loopBody>
  t k|\<rrbracket\>><rsup|\<cal-M\>>>. Given inputs <math|a<rsub|0>\<of\>A>
  and <math|h\<of\><2><rsup|256>>, then in the first clause in the definition
  of <samp|loopBody> we have

  <\equation*>
    <around*|\<llbracket\>|<math-ss|take> t \<vartriangle\>
    <math-ss|IH>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a<rsub|0>,h|\<rangle\>>=\<phi\><rsup|\<cal-M\>><around*|\<langle\>|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a<rsub|0>|)>,\<eta\><rsup|\<cal-M\>><around*|(|h|)>|\<rangle\>>\<of\>\<cal-M\><around*|(|<around*|(|A+B|)>\<times\><2><rsup|256>|)><text|.>
  </equation*>

  It evaluates <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a<rsub|0>|)>>
  and pairs that with <math|h>. For those contexts in which
  <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a<rsub|0>|)>>
  doesn't fail, it results in either an <injl|<around*|(|a<rsub|1>|)>\<of\>A+B>
  for some <math|a<rsub|1>\<of\>A>, or <injr|<around*|(|b|)>\<of\>A+B> from
  some <math|b\<of\>B>. Let us consider the easy case,
  <math|<injr|<around*|(|b|)>>>, first. The remainder of <samp|loopBody>
  continues as follows.

  <\eqnarray*>
    <tformat|<table|<row|<cell|>|<cell|>|<cell|<around*|\<llbracket\>|<samp|case>
    <math|<around*|(|<math-ss|disconnect> <around*|(|<math-ss|assert>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\> <math-ss|OH>|)> k;
    <math|<math-ss|IH>>|)>> <math|<math-ss|OH>>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injr|<around*|(|b|)>>,h|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math|<math-ss|OH>>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|b,h|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|\<eta\><rsup|\<cal-M\>><around*|(|b|)>>>>>
  </eqnarray*>

  Whenever <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a<rsub|0>|)>>,
  ``returns'' a <injr|<around*|(|b|)>> value, that <math|b> value is the
  ``result'' of <math|<around*|\<llbracket\>|<math-ss|loopBody> t
  k|\<rrbracket\>>>, and <math|k> is ignored.

  Now let us consider the case when <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a<rsub|0>|)>>
  results in an <injl|<around*|(|a<rsub|1>|)>> value. In this case the
  remainder of <samp|loopBody> continues as follows.

  <\eqnarray*>
    <tformat|<table|<row|<cell|>|<cell|>|<cell|<around*|\<llbracket\>|<samp|case>
    <math|<around*|(|<math-ss|disconnect> <around*|(|<math-ss|assert>
    <around*|(|<math-ss|IIH> \<vartriangle\> <math-ss|OH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\> <math-ss|IH>|)> k;
    <math|<math-ss|IH>>|)>> <math|<math-ss|OH>>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injl|<around*|(|a<rsub|1>|)>>,h|\<rangle\>>>>|<row||<cell|=>|<cell|<around*|\<llbracket\>|<math|<math-ss|disconnect>
    <around*|(|<math-ss|assert> <around*|(|<math-ss|IIH> \<vartriangle\>
    <math-ss|OH> ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|IH>|)> k; <math|<math-ss|IH>>>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math|<math-ss|IH>>|\<rrbracket\>><rsup|\<cal-M\>>\<leftarrowtail\><around*|\<llbracket\>|<math|<math-ss|disconnect>
    <around*|(|<math-ss|assert> <around*|(|<math-ss|IIH> \<vartriangle\>
    <math-ss|OH> ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|IH>|)> k>|\<rrbracket\>><rsup|\<cal-M\>>|)><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math|<math-ss|IH>>|\<rrbracket\>><rsup|\<cal-M\>>\<leftarrowtail\><around*|\<llbracket\>|<math-ss|take>
    <math-ss|iden> \<vartriangle\> <math-ss|drop>
    k|\<rrbracket\>><rsup|\<cal-M\>>\<leftarrowtail\><around*|\<llbracket\>|<math-ss|assert>
    <around*|(|<math-ss|IIH> \<vartriangle\> <math-ss|OH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|IH>|\<rrbracket\>><rsup|\<cal-M\>>|)><around*|\<langle\>|<cmr|k>,<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math-ss|take>
    <math-ss|iden> \<vartriangle\> <math-ss|drop>
    k;<math-ss|IH>|\<rrbracket\>><rsup|\<cal-M\>>\<leftarrowtail\><around*|\<llbracket\>|<math-ss|assert>
    <around*|(|<math-ss|IIH> \<vartriangle\> <math-ss|OH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|IH>|\<rrbracket\>><rsup|\<cal-M\>>|)><around*|\<langle\>|<cmr|k>,<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math-ss|drop>
    k|\<rrbracket\>><rsup|\<cal-M\>>\<leftarrowtail\><around*|\<llbracket\>|<math-ss|assert>
    <around*|(|<math-ss|IIH> \<vartriangle\> <math-ss|OH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|IH>|\<rrbracket\>><rsup|\<cal-M\>>|)><around*|\<langle\>|<cmr|k>,<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>>>>>
  </eqnarray*>

  For the first part we have

  <\eqnarray*>
    <tformat|<table|<row|<cell|>|<cell|>|<cell|<around*|\<llbracket\>|<math-ss|assert>
    <around*|(|<math-ss|IIH> \<vartriangle\> <math-ss|OH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|IH>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<cmr|k>,<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|\<iota\><rsup|\<cal-M\>><rsub|<maybe>><around*|(|<around*|\<llbracket\>|<math-ss|assert>
    <around*|(|<math-ss|IIH> \<vartriangle\> <math-ss|OH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|IH>|\<rrbracket\>><rsup|<maybe>><around*|\<langle\>|<cmr|k>,<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>|)>>>|<row|<cell|>|<cell|=>|<cell|\<iota\><rsup|\<cal-M\>><rsub|<maybe>><around*|(|\<phi\><rsup|<maybe>><around*|\<langle\>|<around*|\<llbracket\>|<math-ss|assert>
    <around*|(|<math-ss|IIH> \<vartriangle\> <math-ss|OH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)>|\<rrbracket\>><rsup|<maybe>><around*|\<langle\>|<cmr|k>,<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>,\<eta\><rsup|S><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>|)>>>|<row|<cell|>|<cell|=>|<cell|\<iota\><rsup|\<cal-M\>><rsub|<maybe>><around*|(|\<phi\><rsup|<maybe>><around*|\<langle\>|<around*|\<llbracket\>|<math-ss|IIH>
    \<vartriangle\> <math-ss|OH> ;<math-ss|eq><rsub|<2><rsup|256>>|\<rrbracket\>><around*|\<langle\>|<cmr|k>,<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>,\<eta\><rsup|S><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>|)>>>|<row|<cell|>|<cell|=>|<cell|\<iota\><rsup|\<cal-M\>><rsub|<maybe>><around*|(|\<phi\><rsup|<maybe>><around*|\<langle\>|<around*|\<llbracket\>|<math-ss|eq><rsub|<2><rsup|256>>|\<rrbracket\>><around*|\<langle\>|h,<cmr|k>|\<rangle\>>,\<eta\><rsup|S><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>|)>>>>>
  </eqnarray*>

  We know that <math|<around*|\<llbracket\>|<math-ss|eq><rsub|<2><rsup|256>>|\<rrbracket\>><around*|\<langle\>|h,<cmr|k>|\<rangle\>>=<math-tt|1><rsub|<2>>=\<eta\><rsup|S><around*|\<langle\>||\<rangle\>>>
  if and only if <math|h=<cmr|k>> and that
  <math|<around*|\<llbracket\>|<math-ss|eq><rsub|<2><rsup|256>>|\<rrbracket\>><around*|\<langle\>|h,<cmr|k>|\<rangle\>>=<math-tt|0><rsub|<2>>=\<emptyset\><rsup|S>>
  if and only if <math|h\<neq\><cmr|k>>. When <math|h\<neq\><cmr|k>>, then

  <\equation*>
    <around*|\<llbracket\>|<math-ss|assert> <around*|(|<math-ss|IIH>
    \<vartriangle\> <math-ss|OH> ;<math-ss|eq><rsub|<2><rsup|256>>|)>
    \<vartriangle\> <math-ss|IH>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>,<cmr|k>|\<rangle\>>=\<emptyset\><rsup|\<cal-M\>>
  </equation*>

  and the whole <samp|loopBody> expression fails with a
  <math|\<emptyset\><rsup|\<cal-M\>><rsub|B>> result. However, when
  <math|h=<cmr|k>> we have that

  <\equation*>
    <around*|\<llbracket\>|<math-ss|assert> <around*|(|<math-ss|IIH>
    \<vartriangle\> <math-ss|OH> ;<math-ss|eq><rsub|<2><rsup|256>>|)>
    \<vartriangle\> <math-ss|IH>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>,<cmr|k>|\<rangle\>>=\<eta\><rsup|\<cal-M\>><around*|\<langle\>|<around*|\<langle\>||\<rangle\>>,<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>
  </equation*>

  and we can continue with

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|drop>
    k|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<around*|\<langle\>||\<rangle\>>,<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|k|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>>>>>
  </eqnarray*>

  and the result is that

  <\equation*>
    <around*|\<llbracket\>|<samp|case> <math|<around*|(|<math-ss|disconnect>
    <around*|(|<math-ss|assert> <around*|(|<math-ss|IIH> \<vartriangle\>
    <math-ss|OH> ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|IH>|)> k; <math|<math-ss|IH>>|)>>
    <math|<math-ss|OH>>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injl|<around*|(|a<rsub|1>|)>>,h|\<rangle\>>=<around*|\<llbracket\>|k|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a<rsub|1>,h|\<rangle\>><text|.>
  </equation*>

  \;

  Recapping, when <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a<rsub|0>|)>>
  results in an <injl|<around*|(|a<rsub|1>|)>>, then
  <math|<around*|\<llbracket\>|<math-ss|loopBody> t
  k|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a<rsub|0>,h|\<rangle\>>>
  evaluates the continuation <math|<around*|\<llbracket\>|k|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>>
  under the condition that the <math|h> value matches the commitment Merkle
  root of <math|k>, i.e. <math|h=<cmr|k>>, and fails when
  <math|h\<neq\><cmr|k>>.

  Now let us consider <samp|loopBody>'s commitment Merkle root,
  <math|<cmr|<math-ss|loopBody> t k>>. Because of the use of
  <samp|disconnect>, this commitment Merkle root is independent of the
  expression <math|k>.

  <\lemma>
    For all <math|t\<of\>A\<vdash\>A+B> and
    <math|k\<of\>A\<times\><2><rsup|256>\<vdash\>B>,
    <math|<cmr|<math-ss|loopBody> t k>=loopBodyCMR<around*|(|t|)>> where

    <\eqnarray*>
      <tformat|<table|<row|<cell|loopBodyCMR<around*|(|t|)>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|comp>>><rsub|IV>\<comma\>
      <around*|\<langle\>|<cmr|<math-ss|take> t \<vartriangle\>
      <math-ss|IH>>,<next-line>SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|case>>><rsub|IV>\<comma\>
      <around*|\<langle\>|loopTail,<cmr|<math-ss|OH>>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>>>>>
    </eqnarray*>

    and

    <\eqnarray*>
      <tformat|<table|<row|<cell|loopTail>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|comp>>><rsub|IV>\<comma\>
      <around*|\<langle\>|<next-line>SHA256<rsub|Block><around*|\<langle\>|<math|SHA256<rsup|tag<rsup|c><rsub|<math-ss|disconnect>>><rsub|IV>>\<comma\>
      <around*|\<langle\>|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>,<cmr|<math-ss|assert>
      <around*|(|<math-ss|IIH> \<vartriangle\> <math-ss|OH>
      ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
      <math-ss|IH>>|\<rangle\>>|\<rangle\>>,<cmr|<math-ss|IH>>|\<rangle\>>|\<rangle\>><text|.>>>>>
    </eqnarray*>
  </lemma>

  While the commitment Merkle root of <math|<samp|loopBody> t k> does not
  restrict what the continuation <math|k> is, the second component of the
  input to the expression does, since <math|h=<cmr|k>> is required for
  evaluation to be successful. We can build a new expression that forces the
  continuation <math|k> to be <math|<math-ss|loopBody> t k> itself:

  <\render-code>
    <math|<math-ss|loop> t k\<of\>A\<vdash\>B>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|loop>
    t k>>|<cell|:=>|<cell|<math|<math-ss|iden> \<vartriangle\>
    scribe<around*|(|loopBodyCMR<around*|(|t|)>|)>; <math-ss|loopBody> t
    k>>>>>>>>>>>
  </render-code>

  Again, <samp|loop>'s commitment Merkle root is independent of the
  continuation <math|k>:

  <\lemma>
    For all <math|t\<of\>A\<vdash\>A+B> and
    <math|k\<of\>A\<times\><2><rsup|256>\<vdash\>B>,
    <math|<cmr|<math-ss|loop> t k>=loopCMR<around*|(|t|)>> where

    <\eqnarray*>
      <tformat|<table|<row|<cell|loopCMR<around*|(|t|)>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|c><rsub|<math-ss|comp>>><rsub|IV>\<comma\>
      <around*|\<langle\>|<cmr|<math-ss|iden> \<vartriangle\>
      scribe<around*|(|loopBodyCMR<around*|(|t|)>|)>>,loopBodyCMR<around*|(|t|)>|\<rangle\>>|\<rangle\>><text|.>>>>>
    </eqnarray*>
  </lemma>

  By design, <math|<around*|\<llbracket\>|<math-ss|loop> t
  k|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a<rsub|0>|)>> passes
  <math|loopBodyCMR<around*|(|t|)>> as the <math|h> value to
  <math|<math-ss|loopBody> t k>, and the result can only be successful when
  <math|<cmr|k>=loopBodyCMR<around*|(|t|)>=<cmr|<math-ss|loopBody> t
  k<rprime|'>>> for some further continuation
  <math|k<rprime|'>\<of\>A\<times\><2><rsup|256>\<vdash\>B>. Furthermore, the
  same <math|h> value, is passed again into
  <math|><math|<around*|\<llbracket\>|k|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>=<around*|\<llbracket\>|<math-ss|loopBody>
  t k<rprime|'>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>>,
  and that result can only be successful when
  <math|<cmr|k<rprime|'>>=<cmr|<math-ss|loopBody> t k<rprime|''>>> for some
  yet further continuation <math|k<rprime|''>\<of\>A\<times\><2><rsup|256>\<vdash\>B>.

  This process looks endless, making it impossible to redeem any
  loopCMR<around*|(|t|)> commitment. However we can end this chain by using

  <\render-code>
    <math|<math-ss|loopEnd> t\<of\>A\<times\><2><rsup|256>\<vdash\>B>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|loopEnd>
    t>>|<cell|:=>|<cell|<math|<math-ss|take> t \<vartriangle\>
    <math-ss|IH>>>>|<row|<cell|>|<cell|;>|<cell|<samp|assertr>
    <math|loopTail> <math|<math-ss|OH>>>>>>>>>>>>
  </render-code>

  The <math|<samp|loopEnd> t> expression replaces the <samp|case> combinator
  in <math|<samp|loopBody> t> with an assertion that
  <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a<rsub|n>|)>>
  results in a <math|<injr|<around*|(|b|)>>>. By construction
  <math|<cmr|<math-ss|loopEnd> t>=loopBodyCMR<around*|(|t|)>>, so that it can
  be used as a final continuation to terminate our chain of expressions in
  <math|<math-ss|loop> t k>.

  Tying everything together, we have a commitment Merkle root,
  <math|loopCMR<around*|(|t|)>>, that makes a commitment to a subexpression
  that can be redeemed by a subexpression of the form

  <\equation*>
    <math-ss|loop> t <around*|(|<math-ss|loopBody> t
    <around*|(|<math-ss|loopBody> t <around*|(|\<ldots\><around*|(|<math-ss|loopBody>
    t <around*|(|<math-ss|loopEnd> t|)>|)>|)>|)>|)>
  </equation*>

  where <samp|loopBody> is repeated the number of times necessary for
  <math|<around*|\<llbracket\>|t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a<rsub|n>|)>>
  to result in a <math|<injr|<around*|(|b|)>>> value in the particular
  redemption context. Note that while it appears that <math|t> is duplicated
  <math|n> times, the subexpression <math|t> will be shared in a DAG
  representation of this expression, avoiding a large of a blow up in program
  size.

  We have repeated the same expression <math|t> in during redemption in the
  above example; however, if the <math|t> expression contains <samp|witness>
  subexpressions, those witness values could be different for each instance
  of <math|t> shown above. Thus, more generally, the commitment can be
  redeemed by

  <\equation*>
    <math-ss|loop> t<rsub|0> <around*|(|<math-ss|loopBody> t<rsub|1>
    <around*|(|<math-ss|loopBody> t<rsub|2>
    <around*|(|\<ldots\><around*|(|<math-ss|loopBody> t<rsub|n-1>
    <around*|(|<math-ss|loopEnd> t<rsub|n>|)>|)>|)>|)>|)>
  </equation*>

  when <math|<cmr|t<rsub|i>>=<cmr|t>> for all <math|i>. For example, this
  construction would let you build a Simplicity expression that takes an
  arbitrarily long stream of SHA-256's 512 bit data blocks and computes the
  SHA-256 compression function composed over this stream of blocks by putting
  each data block into a <samp|witness> expression within the different
  <math|t<rsub|i>>'s.

  <subsection|Adding a <samp|loop> primitive to Simplicity?>

  The purpose of the above derivation of the <samp|loop> construction is to
  understand the theoretical expressiveness that Simplicity's delegation
  extension adds to the language. The <samp|loop> construction proves that
  the delegation extension brings Simplicity's expressiveness beyond what is
  possible with full Simplicity without delegation.

  While it is, in principle, possible to use the <samp|loop> construction in
  Simplicity applications (that support the delegation extension), the
  <samp|loop> construction is subject to all the same problems that using
  delegation entails: One cannot bound the computation costs of redemption at
  commitment time using general purpose static analysis. One might be able to
  perform an ad-hoc analysis on a particular program in order to bound the
  computation costs, but there are programs you can write in Simplicity with
  delegation where no upper bound on redemption costs exists. As with
  <samp|disconnect>, using <samp|loop> risks creating program that ends up
  impractical to redeem due to costs. Therefore we strongly recommend against
  using <samp|loop> in practice.

  If, contrary to our expectations, the <samp|loop> construction ends up very
  popular, we could amend the specification of Simplicity to add native
  <math|<samp|loop> t k> and <math|<math-ss|loopEnd> t> combinators to
  Simplicity such that their commitment Merkle roots that depends only on
  <math|t>, and with rules that require the continuation <math|k> be one of
  the two <samp|loop> constructors (with the same <math|t> parameter). This
  would somewhat reduce the overhead of using unbounded loops.

  <section|Universal Signature Hash Modes><label|ss:UniversalSignatureHashModes>

  In Section<nbsp><reference|ss:checkSigHashAll> we defined a Simplicity
  Program for a single signature check with over fixed <samp|hashAll>
  transaction digest message. However, in Bitcoin Script, the user can select
  among a set of multiple different signature hash modes. Moreover, this
  choice is made at redeption time rather than at commitment time. We could
  replicate this behaviour by writing a Simplicity program that, given a
  signature hash flag value defined by a <samp|witness> node, selects amongst
  a small variety of transaction digest expressions to use. However by using
  <samp|disconnect>, we can provide the user with an unlimited choice of
  signature hash modes.

  Below we define <math|<samp|sigHash> t> where
  <math|t\<of\><1>\<vdash\><2><rsup|256>> is a Simplicity expression that
  defines some signature hash mode.

  <\render-code>
    <math|<math-ss|sigHash> t\<of\><1>\<vdash\><2><rsup|256>>

    <math|<tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|4|2|2|cell-halign|r>|<cwith|4|4|2|2|cell-halign|r>|<table|<row|<cell|<math-ss|sigHash>
    t>|<cell|:=>|<cell|<math-ss|scribe><around*|(|SHA256<rsub|IV><rsup|<math-tt|[<SimplicityPrefix>1f5369676e6174757265]>>|)>>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|<samp|disconnect>
    <math-ss|iden> t>>|<row|<cell|>|<cell|;>|<cell|<math-ss|sha256-block>)<math|\<vartriangle\>><math-ss|scribe><around*|(|<around*|\<lfloor\>|2<rsup|511>+1024|\<rfloor\>><rsub|512>|)>>>|<row|<cell|>|<cell|;>|<cell|<math-ss|sha256-block>>>>>>>>>>>>
  </render-code>

  This expression can be composed with pubkey key and signature values to
  form a Simplicity program that supports universal signature hash modes.

  <\render-code>
    <math|<around*|(|<math-ss|checkSigHash>
    t|)><around*|\<langle\>|p,s|\<rangle\>>\<of\><1>\<vdash\><1>>

    <math|<tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<around*|(|<math-ss|checkSigHash>
    t|)>><around*|\<langle\>|p,s|\<rangle\>>>|<cell|:=>|<cell|<around*|(|<math-ss|scribe><rsub|PubKey><around*|(|p|)><math|<math|>\<vartriangle\>><math-ss|sigHash>
    t|)> \<vartriangle\> <math-ss|witness><rsub|Sig><around*|(|s|)>>>|<row|<cell|>|<cell|;>|<cell|<math-ss|bip0340-verify>>>>>>>>>>>>
  </render-code>

  The <math|<math-ss|sigHash> t> expression is similar to the definition of
  <samp|sigHashAll> from Section<nbsp><reference|ss:checkSigHashAll>. \ The
  difference is that we have replaced the
  <math|<around*|(|<samp|scribe><around*|(|<math|<cmr|<math-ss|hashAll>>>|)><math|\<vartriangle\>><samp|hashAll>|)>>
  subexpression with <math|<samp|disconnect> <math-ss|iden> t>. \ When
  <math|t> is <samp|hashAll>, these two expressions have identical semantics:

  <\eqnarray*>
    <tformat|<table|<row|<cell|>|<cell|>|<cell|<around*|\<llbracket\>|<samp|disconnect>
    <math-ss|iden> <math-ss|hashAll>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math-ss|scribe><around*|(|<cmr|<math-ss|hashAll>>|)>\<vartriangle\>
    <math|<math-ss|iden>>;<math-ss|iden>;<math-ss|take> <math-ss|iden>
    \<vartriangle\> <math-ss|drop> <math-ss|hashAll>|\<rrbracket\>><rsup|<BC>>|)><around*|\<langle\>||\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math-ss|take>
    <math-ss|iden> \<vartriangle\> <math-ss|drop>
    <math-ss|hashAll>|\<rrbracket\>><rsup|<BC>>\<leftarrowtail\>\<eta\><rsup|BC>\<leftarrowtail\><around*|\<llbracket\>|<math-ss|scribe><around*|(|<cmr|<math-ss|hashAll>>|)>\<vartriangle\>
    <math|<math-ss|iden>>|\<rrbracket\>><rsup|<BC>>|)><around*|\<langle\>||\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math-ss|take>
    <math-ss|iden> \<vartriangle\> <math-ss|drop>
    <math-ss|hashAll>|\<rrbracket\>><rsup|<BC>>\<leftarrowtail\><around*|\<llbracket\>|<math-ss|scribe><around*|(|<cmr|<math-ss|hashAll>>|)>\<vartriangle\>
    <math|<math-ss|iden>>|\<rrbracket\>><rsup|<BC>>|)><around*|\<langle\>||\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math-ss|take>
    <math-ss|iden> \<vartriangle\> <math-ss|drop>
    <math-ss|hashAll>|\<rrbracket\>><rsup|<BC>>\<leftarrowtail\>\<eta\><rsup|BC>\<circ\><around*|\<llbracket\>|<math-ss|scribe><around*|(|<cmr|<math-ss|hashAll>>|)>\<vartriangle\>
    <math|<math-ss|iden>>|\<rrbracket\>>|)><around*|\<langle\>||\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math-ss|take>
    <math-ss|iden> \<vartriangle\> <math-ss|drop>
    <math-ss|hashAll>|\<rrbracket\>><rsup|<BC>>\<circ\><around*|\<llbracket\>|<math-ss|scribe><around*|(|<cmr|<math-ss|hashAll>>|)>\<vartriangle\>
    <math|<math-ss|iden>>|\<rrbracket\>>|)><around*|\<langle\>||\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|take>
    <math-ss|iden> \<vartriangle\> <math-ss|drop>
    <math-ss|hashAll>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>|<around*|\<llbracket\>|<math-ss|scribe><around*|(|<cmr|<math-ss|hashAll>>|)>|\<rrbracket\>><around*|\<langle\>||\<rangle\>>,<around*|\<langle\>||\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|\<phi\><around*|\<langle\>|<around*|(|\<eta\><rsup|BC>\<circ\><around*|\<llbracket\>|<math-ss|scribe><around*|(|<cmr|<math-ss|hashAll>>|)>|\<rrbracket\>>|)><around*|\<langle\>||\<rangle\>>,<around*|\<llbracket\>|
    <math-ss|hashAll>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|\<phi\><around*|\<langle\>|<around*|\<llbracket\>|<math-ss|scribe><around*|(|<cmr|<math-ss|hashAll>>|)>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>,<around*|\<llbracket\>|
    <math-ss|hashAll>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>|\<rangle\>>>>|<row|<cell|>|=|<cell|<around*|\<llbracket\>|<samp|scribe><around*|(|<cmr|<math-ss|hashAll>>|)><math|\<vartriangle\>><samp|hashAll>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>>>>>>
  </eqnarray*>

  The difference between the two expressions is that the subexpression
  <math|<samp|disconnect> <math-ss|iden> <math-ss|hashAll>> does not commit
  to using the <math|<math-ss|hashAll>> transaction digest. \ During
  redemption any alternative expression \ <math|t\<of\><1>\<vdash\><2><rsup|256>>
  for creating a digest can be used instead. \ Because <math|<cmr|t>> is
  covered by the digital signature proveded to <math|<samp|checkSigHash> t>,
  the signature fixes the digest expression and it cannot be altered by a
  third party while still satisfying the <math|<math-ss|bip0340-verify>>,
  with the exception of any <samp|witness> values or <samp|disconnect>ed
  expressions within <math|t>. This allows users not only to simulate any of
  Script's signature hash flags, but to create and use any novel signtature
  hash mode that they desire.

  <subsection|Side-Effects and Delegation>

  While the primary purpose of the <math|t\<of\><1>\<vdash\><2><rsup|256>>
  parameter in <math|<math-ss|checkSigHash> t> is to use the Bitcoin
  primitives (or more generally the primitives for the specific blockchain
  application being used) to construct a cryptographic digest, the <math|t>
  parameter can additionally include assertion side-effects. \ For example,
  one could include a condition that an absolute or relative timelock meets
  some specific threshold, without the signature covering any specific
  timelock value in the digest.

  Another possibility is to have the expression return a trivial value (e.g.
  <math|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>>) and have <math|t>
  itself contain its own <math|<around*|(|<samp|checkSigHash>
  t<rprime|'>|)><around*|\<langle\>|p<rprime|'>,s<rprime|'>|\<rangle\>>>
  program for a different public key and its own digest expression
  <math|t<rprime|'>>. \ The side-effect of the <math|<math-ss|schnorrAssert>>
  within this inner <samp|checkSigHash> expression essures that the whole
  Simplicity expression is only successfull if the signature
  <math|s<rprime|'>> is valid for the public key <math|p<rprime|'>> and for
  the transaction digest <math|t<rprime|'>>. This process lets you delegate
  control to another public key by creating a signature with the orginal
  public key that covers such a delegaton mode for a specific public key,
  <math|p<rprime|'>>. \ Further conditions can be added as to such a
  delegation such as checks to limit the amount of funds being spent while
  ensuring the change is send back to a fixed address. \ Such delegation can
  be recursively applied, but could also be restricted by delgating to
  <math|<around*|(|<samp|checkSigHashAll>|)><around*|\<langle\>|p<rprime|'>,s<rprime|'>|\<rangle\>>>
  or to some other fixed set of signature hash modes instead.

  Using <math|<around*|(|<samp|checkSigHash>
  t|)><around*|\<langle\>|p,s|\<rangle\>>> as a standard Simplicity
  expression gives users maximal control over how they are able to later
  redeem their funds.<chapter|Type Inference and Serialization>

  In this chapter we will define a representation of Simplicity expressions
  as an untyped Simplicity DAG where subexpressions have explicit sharing. We
  will define how to perform type inference and reconstruct a Simplicity
  expression from this Simplicity DAG and we will define a binary
  serialization format for these Simplicity DAGs.

  <section|Explicit Simplicity DAGs><label|ss:DAGs>

  In this section, we will introduce an DAG representation for (untyped)
  Simplicity expressions with explicit sharing of subexpressions. A
  Simplicity DAG is a topologically sorted list of Simplicity nodes. Each
  Simplicity node is a combinator name with a payload of references to
  earlier nodes in the list, or a payload of witness data, etc.

  First we enumerate the possible values for Simplicity nodes.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<cwith|1|1|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-col-span|1>|<table|<row|<cell|<math|<math-ss|`iden'>\<of\>Node>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<cwith|1|1|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-col-span|1>|<table|<row|<cell|<math|<math-ss|`unit'>\<of\>Node>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|i\<of\>\<bbb-N\>>>>>>>>>|<row|<cell|<math|<math-ss|`injl'>
    i\<of\>Node>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|i\<of\>\<bbb-N\>>>>>>>>>|<row|<cell|<math|<math-ss|`injr'>
    i\<of\>Node>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|i\<of\>\<bbb-N\>>>>>>>>>|<row|<cell|<math|<math-ss|`take'>
    i\<of\>Node>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|i\<of\>\<bbb-N\>>>>>>>>>|<row|<cell|<math|<math-ss|`drop'>
    i\<of\>Node>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|i\<of\>\<bbb-N\>>>|<cell|<math|j\<of\>\<bbb-N\>>>>>>>>>|<row|<cell|<math|<math-ss|`comp'>
    i j\<of\>Node>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|i\<of\>\<bbb-N\>>>|<cell|<math|j\<of\>\<bbb-N\>>>>>>>>>|<row|<cell|<math|<math-ss|`case'>
    i j\<of\>Node>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|i\<of\>\<bbb-N\>>>|<cell|<math|j\<of\>\<bbb-N\>>>>>>>>>|<row|<cell|<math|<math-ss|`pair'>
    i j\<of\>Node>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|i\<of\>\<bbb-N\>>>|<cell|<math|j\<of\>\<bbb-N\>>>>>>>>>|<row|<cell|<math|<math-ss|`disconnect'>
    i j\<of\>Node>>>>>>

    \;
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|v\<of\><2><rsup|\<ast\>>>>>>>>>>|<row|<cell|<math|<math-ss|`witness'>
    v\<of\>Node>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|b\<of\><2><rsup|512>>>>>>>>>|<row|<cell|<math|<math-ss|`fail'>
    b\<of\>Node>>>>>>
  </with>

  \;

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|h\<of\><2><rsup|256>>>>>>>>>|<row|<cell|<math|<math-ss|`hidden'>
    h\<of\>Node>>>>>>
  </with>

  \;

  In addition to the above, every primitive name is a Node. This set of
  primitives is application specific. For Simplicity with Bitcoin, we have
  <math|<math-ss|`version'>\<of\>Node>, <math|<math-ss|`lockTime'>\<of\>Node>,
  etc.

  The single quotes around the Node names is there to distinguish them from
  their corresponding Simplicity combinator. Notice that there is not a
  perfect 1-to-1 relationship between Node names and Simplicity combinators.
  In particular, there are no Node names for the <samp|assertl> and
  <samp|assertr> combinators. Instead we have one <samp|`hidden'> Node name
  that will be used in conjunction with <samp|`case'> to represent
  assertions.

  A Simplicity DAG is represented as a topologically sorted, (non-empty) list
  of Nodes. (You may wish to review Section<nbsp><reference|ss:ListFunctors>
  to recall our notation for list related operators.)

  <\equation*>
    DAG\<assign\>Node<rsup|+>
  </equation*>

  Each node has between 0 and 2 references to nodes found earlier in the list
  represented by a relative offset.

  <\eqnarray*>
    <tformat|<table|<row|<cell|ref<around*|(|<math-ss|`iden'>|)>>|<cell|\<assign\>>|<cell|\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`unit'>|)>>|<cell|\<assign\>>|<cell|\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`injl'>
    i|)>>|<cell|\<assign\>>|<cell|i\<blacktriangleleft\>\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`injr'>
    i|)>>|<cell|\<assign\>>|<cell|i\<blacktriangleleft\>\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`take'>
    i|)>>|<cell|\<assign\>>|<cell|i\<blacktriangleleft\>\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`drop'>
    i|)>>|<cell|\<assign\>>|<cell|i\<blacktriangleleft\>\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`comp'>
    i j|)>>|<cell|\<assign\>>|<cell|i\<blacktriangleleft\>j\<blacktriangleleft\>\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`case'>
    i j|)>>|<cell|\<assign\>>|<cell|i\<blacktriangleleft\>j\<blacktriangleleft\>\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`pair'>
    i j|)>>|<cell|\<assign\>>|<cell|i\<blacktriangleleft\>j\<blacktriangleleft\>\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`disconnect'>
    i j|)>>|<cell|\<assign\>>|<cell|i\<blacktriangleleft\>j\<blacktriangleleft\>\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`witness'>
    v|)>>|<cell|\<assign\>>|<cell|\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`fail'>
    b|)>>|<cell|\<assign\>>|<cell|\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`hidden'>
    h|)>>|<cell|\<assign\>>|<cell|\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`version'>|)>>|<cell|\<assign\>>|<cell|\<epsilon\>>>|<row|<cell|ref<around*|(|<math-ss|`lockTime'>|)>>|<cell|\<assign\>>|<cell|\<epsilon\>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>>>
  </eqnarray*>

  In order for a list <math|l:DAG> to be well-formed, it must satisfy two
  conditions. Firstly, we require that references only have offsets that
  refer to nodes occurring strictly earlier in the list:

  <\equation*>
    \<forall\><around*|\<langle\>|k,a|\<rangle\>>\<in\>indexed<around*|(|l|)>\<point\>\<forall\>i\<in\>ref<around*|(|a|)>\<point\>0\<less\>i\<leq\>k
  </equation*>

  Secondly, when <math|<math-ss|`hidden'>> a node is a child, the parent must
  be a <math|<math-ss|`case'>> node, which in turn can only have at most one
  <math|<math-ss|`hidden'>> child node.

  <\equation*>
    \<forall\><around*|\<langle\>|k,a|\<rangle\>>\<in\>indexed<around*|(|l|)>\<point\>\<forall\>i\<in\>ref<around*|(|a|)>\<point\>
    \<forall\>h.l<around*|[|k-i|]>=\<eta\><rsup|S><around*|(|<math-ss|`hidden'>
    h|)>\<Rightarrow\> \<exists\> j<rsub|1> j<rsub|2>. a=<math-ss|`case'>
    j<rsub|1> j<rsub|2>
  </equation*>

  and

  <\equation*>
    \<forall\><around*|\<langle\>|k,<math-ss|`case'> i<rsub|>
    j|\<rangle\>>\<in\>indexed<around*|(|l|)>\<point\>\<forall\>h<rsub|1>h<rsub|2>.l<around*|[|k-i|]>\<neq\>\<eta\><rsup|S><around*|(|<math-ss|`hidden'>
    h<rsub|1>|)>\<vee\>l<around*|[|k-j|]>\<neq\>\<eta\><rsup|S><around*|(|<math-ss|`hidden'>
    h<rsub|2>|)>
  </equation*>

  <\theorem>
    If a list <math|l:DAG> is well-formed, and <math|l<rsub|0>:DAG> is a
    prefix of <math|l> (i.e. there exists an <math|l<rsub|1>> such that
    <math|\<eta\><rsup|S><around*|(|l<rsub|0>|)>\<cdummy\>l<rsub|1>=\<eta\><rsup|S><around*|(|l|)>>)
    then <math|l<rsub|0>> is also well-formed.
  </theorem>

  Note that technically the root of a well-formed DAG,
  <math|l<around*|[|<around*|\||l|\|>-1|]>>, can be a
  <math|<math-ss|`hidden'>> node.

  <subsection|Type Inference><label|ss:typeInference>

  Simplicity DAGs, as described above, do not have type information
  associated with them. Before we can interpret a Simplicity DAG as a
  Simplicity expression we must first perform type inference. Type inference
  can be done by solving unification equations of typing constraints to
  compute a most general unifier.

  A unification equation is written as <math|S\<doteq\>T> were <math|S> and
  <math|T> are Simplicity type expressions with unification variables, where
  unification variables are denoted by Greek letters <math|\<alpha\>>,
  <math|\<beta\>>, <math|\<gamma\>>, etc.

  Given a well-formed <math|l:DAG>, we associate with each index in the list,
  <math|0\<leq\>k\<less\><around*|\||l|\|>>, a pair of fresh unification
  variables <math|\<alpha\><rsub|k>,\<beta\><rsub|k>> that are to be
  instantiated at the inferred source and target types of the expression for
  the node at index <math|k>. Each different node occurring at an index
  <math|k> in the DAG <math|l> implies a set of unification equations over
  these type variables, possibly requiring further fresh unification
  variables.

  <\eqnarray*>
    <tformat|<table|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`iden'>|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{|\<alpha\><rsub|k>\<doteq\>\<beta\><rsub|k>|}>>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`unit'>|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{|\<beta\><rsub|k>\<doteq\><1>|}>>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`injl'>
    i|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{|\<alpha\><rsub|k>\<doteq\>\<alpha\><rsub|k-i>,\<beta\><rsub|k>\<doteq\>\<beta\><rsub|k-i>+\<gamma\>|}>*<htab|5mm>where
    \<gamma\> is fresh>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`injr'>
    i|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{|\<alpha\><rsub|k>\<doteq\>\<alpha\><rsub|k-i>,\<beta\><rsub|k>\<doteq\>\<gamma\>+\<beta\><rsub|k-i>|}>*<htab|5mm>where
    \<gamma\> is fresh>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|<math|>`take'>
    i|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{|\<alpha\><rsub|k>\<doteq\>\<alpha\><rsub|k-i>\<times\>\<gamma\>,\<beta\><rsub|k>\<doteq\>\<beta\><rsub|k-i>|}>*<htab|5mm>where
    \<gamma\> is fresh>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`drop'>
    i|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{|\<alpha\><rsub|k>\<doteq\>\<gamma\>\<times\>\<alpha\><rsub|k-i>,\<beta\><rsub|k>\<doteq\>\<beta\><rsub|k-i>|}>*<htab|5mm>where
    \<gamma\> is fresh>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`comp'>
    i j|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{|\<alpha\><rsub|k>\<doteq\>\<alpha\><rsub|k-i>,\<beta\><rsub|k-i>\<doteq\>\<alpha\><rsub|k-j>,\<beta\><rsub|k>\<doteq\>\<beta\><rsub|k-j>|}>>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`case'>
    i j|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{|\<alpha\><rsub|k>\<doteq\><around*|(|\<gamma\><rsub|1>+\<gamma\><rsub|2>|)>\<times\>\<gamma\><rsub|3>|}><next-line>\<cup\><around*|{|\<alpha\><rsub|k-i>\<doteq\>\<gamma\><rsub|1>\<times\>\<gamma\><rsub|3>,\<beta\><rsub|k>\<doteq\>\<beta\><rsub|k-i>\|\<forall\>h.l<around*|[|k-i|]>\<neq\>\<eta\><rsup|S><around*|(|<math-ss|`hidden'>
    h|)>|}><htab|5mm><next-line>\<cup\><around*|{|a<rsub|k-j>\<doteq\>\<gamma\><rsub|2>\<times\>\<gamma\><rsub|3>,\<beta\><rsub|k>\<doteq\>\<beta\><rsub|k-j>\|\<forall\>h.l<around*|[|k-j|]>\<neq\>\<eta\><rsup|S><around*|(|<math-ss|`hidden'>
    h|)>|}><next-line><htab|5mm>where \<gamma\><rsub|1>,\<gamma\><rsub|2>,\<gamma\><rsub|3>
    are fresh>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`pair'>
    i j|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{|\<alpha\><rsub|k>\<doteq\>\<alpha\><rsub|k-i>\<doteq\>\<alpha\><rsub|k-j>,\<beta\><rsub|k>\<doteq\>\<beta\><rsub|k-i>\<times\>\<beta\><rsub|k-j>|}>>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`disconnect'>
    i j|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{|\<alpha\><rsub|k-i>\<doteq\>\<alpha\><rsub|k>\<times\><2><rsup|256>,\<beta\><rsub|k-i>\<doteq\>\<gamma\>\<times\>\<alpha\><rsub|k-j>,\<beta\><rsub|k>\<doteq\>\<gamma\>\<times\>\<beta\><rsub|k-j>|}>*<htab|5mm>where
    \<gamma\> is fresh>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`witness'>
    v|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{||}>>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`fail'>
    b|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{||}>>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`hidden'>
    h|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{||}>>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`version'>|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{|\<alpha\><rsub|k>\<doteq\><1>,\<beta\><rsub|k>\<doteq\><2><rsup|32>|}>>>|<row|<cell|con<rsub|l><around*|\<langle\>|k,<math-ss|`lockTime'>|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|{|\<alpha\><rsub|k>\<doteq\><1>,\<beta\><rsub|k>\<doteq\>Lock|}>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>>>
  </eqnarray*>

  The rest of the constraints for the other Bitcoin primitive names follows
  the same pattern of adding constraints for the <math|\<alpha\><rsub|k>> and
  <math|\<beta\><rsub|k>> variables to be equal to the input and output types
  of the corresponding primitives, all of which are required to be concrete
  types.

  Notice that the unification variables for <samp|`hidden'> nodes are unused.
  When <samp|`hidden'> nodes occur as children, their parent must be a
  <samp|`case'> node and the constraints for <samp|`case'> nodes specifically
  excludes references to their <samp|`hidden'> children's unification
  variables. Thus when a <samp|`case'> node represents an assertion, the only
  type constraints needed for an assertion are added.

  Using the <math|con<rsub|l>> function, we can collect all the constraints
  that need to be solved for a well-formed (untyped) Simplicity DAG,
  <math|l:DAG>, to be well-typed:

  <\equation*>
    con<around*|(|l|)>\<assign\>fold<rsup|<op|\<cup\>>><around*|(|con<rsub|l><rsup|+><around*|(|indexed<around*|(|l|)>|)>|)>
  </equation*>

  Depending on the application there may be further constraints imposed on
  the root of the DAG. For example, if the DAG is supposed to represent a
  Simplicity program, which has type <math|<1>\<vdash\><1>>, we would also
  add the constraints <math|<around*|{|\<alpha\><rsub|<around*|\||l|\|>-1>\<doteq\><1>,\<beta\><rsub|<around*|\||l|\|>-1>\<doteq\><1>|}>>.

  A <dfn|substitution> <math|\<varsigma\>> is a function from unification
  variables to Simplicity type expressions with unification variables. A
  substitution, <math|\<varsigma\>>, is a <dfn|ground substitution> if for
  every unification variable <math|\<alpha\>>, the Simplicity type
  <math|\<varsigma\><around*|(|\<alpha\>|)>> has no unification variables. A
  substitution, <math|\<varsigma\>>, applied to Simplicity type expression
  <math|S>, is a new Simplicity type expression <math|S\|<rsub|\<varsigma\>>>
  with each unification variable <math|\<alpha\>> replaced by
  <math|\<varsigma\><around*|(|\<alpha\>|)>>:

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<alpha\>\|<rsub|\<varsigma\>>>|<cell|\<assign\>>|<cell|\<varsigma\><around*|(|\<alpha\>|)>>>|<row|<cell|<1>\|<rsub|\<varsigma\>>>|<cell|\<assign\>>|<cell|<1>>>|<row|<cell|<around*|(|S+T|)>\|<rsub|\<varsigma\>>>|<cell|\<assign\>>|<cell|S<mid|\|><rsub|\<varsigma\>>+T<mid|\|><rsub|\<varsigma\>>>>|<row|<cell|<around*|(|S\<times\>T|)>\|<rsub|\<varsigma\>>>|<cell|\<assign\>>|<cell|S<mid|\|><rsub|\<varsigma\>>\<times\>T<mid|\|><rsub|\<varsigma\>>>>>>
  </eqnarray*>

  A substitution <math|\<tau\>> can also be applied to other substitutions
  yielding a composite substitution:

  <\equation*>
    \<varsigma\>\|<rsub|\<tau\>><around*|(|\<alpha\>|)>\<assign\>\<varsigma\><around*|(|\<alpha\>|)>\|<rsub|\<tau\>>
  </equation*>

  A substitution <math|\<varsigma\><rsub|1>> is an instance of another
  substitution <math|\<varsigma\><rsub|2>> whenever there exists a
  substitution <math|\<tau\>> such that <math|\<varsigma\><rsub|1>=\<varsigma\><rsub|2>\|<rsub|\<tau\>>>.
  If <math|\<varsigma\><rsub|1>> and <math|\<varsigma\><rsub|2>> are both
  instances of each other then they are <math|\<alpha\>>-equivalent.

  A unifier for a set of constraints <math|C> is a substitution
  <math|\<varsigma\>> such that for every constraint
  <math|<around*|(|S\<doteq\>T|)>\<in\>C> we have
  <math|S<around|\||<rsub|\<varsigma\>>= T|\|><rsub|\<varsigma\>>>. The most
  general unifier for a set of constraints is a unifier <math|\<varsigma\>>
  for those constraints such that every other unifier
  <math|\<varsigma\><rprime|'>> for those constraints is an instance of
  <math|\<varsigma\>>. The most general unifier is unique up to
  <math|\<alpha\>>-equivalence.

  Once all the constraints have be gathered we can perform first-order
  unification to solve for the most general unifier <math|\<varsigma\>>. The
  most general unifier, <math|\<varsigma\>>, may still contain free
  variables. To eliminate these free variables, we define an instance of
  <math|\<varsigma\>> that sets all remaining free variable to the unit type
  <1>. We call the resulting ground substitution
  <math|\<varsigma\><rsub|<1>>>:

  <\equation*>
    \<varsigma\><rsub|<1>>\<assign\>\<varsigma\>\|<rsub|\<lambda\>\<gamma\>.<1>>
  </equation*>

  Notice that if <math|\<varsigma\>> and <math|\<tau\>> are
  <math|\<alpha\>>-equivalent then <math|\<varsigma\><rsub|<1>>=\<tau\><rsub|<1>>>.
  In particular, this means that the ground substitution
  <math|\<varsigma\><rsub|<1>>> is independent of which choice of
  <math|\<varsigma\>> we compute as the most general unifier.

  It is possible that there is no unifier for the given collection of
  constraints. In such a case the Simplicity DAG is ill-typed, (or does not
  meet the type constraints imposed by the application) and does not
  represent a well-typed Simplicity expression.

  First-order unification can be preformed time linear in the size of the
  constraints<nbsp><cite|unification>, although in practice quasi-linear time
  algorithms using the union-find algorithm are simpler and may perform
  better on the size of problems one is likely to encounter. Our set of
  constraints is linear in the size of the DAG thus we can compute the most
  general unifier in linear (or quasi-linear) time.

  It is important to note that these (quasi-)linear time computations rely on
  having sharing of (type) subexpressions in the representation of the
  substitution. If you flatten out the representation of the substitution,
  for example by printing out all the types, the result can be exponential in
  the size of the input DAG. Fortunately, all of the computation required for
  Simplicity's consensus operations, can operate without flattening the
  representation of the inferred types.

  Also notice that our set of constraints imply we are doing monomorphic type
  inference, meaning that any shared subexpressions are assigned the same
  type. Sometimes we will require multiple instances of the same sub-DAG
  within a DAG so that different types can be inferred for the subexpressions
  corresponding to those sub-DAG. As a trivial example, a DAG will often have
  multiple <samp|`iden'> nodes, one for each type that the <samp|iden>
  combinator is be used for. A DAG should never have sub-DAGs that end up
  with the same pair of inferred types and will be disallowed by
  anti-malleability rules (see Section<nbsp><inactive|<reference|<with|color|red|TODO>>>).

  \ We could remove duplicate sub-DAGs entirely by using polymorphic type
  inference instead. Polymorphic type inference is
  DEXPTIME-complete<nbsp><cite|Mairson:1989>. However, because removing
  duplicated sub-DAGs can produce exponentially smaller terms it might be the
  case that polymorphic type inference is linear in the size of the DAG with
  duplicated sub-DAGs that are needed for monomorphic type inference. If this
  is the case, we could switch to polymorphic type inference without opening
  up DoS attacks. Whether this is possible or not is currently open question
  for me.

  <subsection|Reconstructing Simplicity Expressions>

  Given a well-formed Simplicity DAG, <math|l:DAG>, that does have a
  substitution <math|\<varsigma\>> yielding the most general unifier for
  <math|con<around*|(|l|)>>, we can attempt to synthesize the Simplicity
  expression that the DAG represents by recursively interpreting the DAG as
  <math|syn<around*|(|l|)>\<of\>\<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|<around*|\||l|\|>-1>|)>\<vdash\>\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|<around*|\||l|\|>-1>|)>>
  where

  <\equation*>
    syn<around*|(|l|)>\<assign\>syn<around*|(|l,<around*|\||l|\|>-1,l<around*|[|<around*|\||l|\|>-1|]>|)>
  </equation*>

  and where

  <\eqnarray*>
    <tformat|<table|<row|<cell|syn<around*|(|l,k,\<emptyset\><rsup|<maybe>>|)>>|<cell|\<assign\>>|<cell|\<bot\>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`iden'>|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|iden><rsub|\<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k>|)>>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`unit'>|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|unit><rsub|\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k>|)>>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`injl'>
    i|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|injl><rsub|\<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k>|)>,B,C>
    syn<around*|(|l,k-i,l<around*|[|k-i|]>|)>*<htab|5mm>where
    B+C=\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k>|)>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`injr'>
    i|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|injr><rsub|\<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k>|)>,B,C>
    syn<around*|(|l,k-i,l<around*|[|k-i|]>|)>*<htab|5mm>where
    B+C=\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k>|)>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`take'>
    i|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|take><rsub|A,B,\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k>|)>>
    syn<around*|(|l,k-i,l<around*|[|k-i|]>|)>*<htab|5mm>where
    A\<times\>B=\<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k>|)>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`drop'>
    i|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|drop><rsub|A,B,\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k>|)>>
    syn<around*|(|l,k-i,l<around*|[|k-i|]>|)>*<htab|5mm>where
    A\<times\>B=\<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k>|)>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`comp'>
    i j|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|comp><rsub|\<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k>|)>,\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k-i>|)>,\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k>|)>>
    syn<around*|(|l,k-i,l<around*|[|k-i|]>|)>
    syn<around*|(|l,k-j,l<around*|[|k-j|]>|)>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`case'>
    i j|)>|)>>|<cell|\<assign\>>|<cell|syncase<around*|(|l,k,k-i,l<around*|[|k-i|]>,k-j,l<around*|[|k-j|]>|)>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`pair'>
    i j|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|pair><rsub|\<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k>|)>,\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k-i>|)>,\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k-j>|)>>
    syn<around*|(|l,k-i,l<around*|[|k-i|]>|)>
    syn<around*|(|l,k-j,l<around*|[|k-j|]>|)>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`disconnect'>
    i j|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|disconnect><rsub|\<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k>|)>,B,C,\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k-j>|)>>
    syn<around*|(|l,k-i,l<around*|[|k-i|]>|)>
    syn<around*|(|l,k-j,l<around*|[|k-j|]>|)><next-line><htab|5mm>where
    B\<times\>C=\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k-i>|)>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`witness'>
    v|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|witness><rsub|\<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k>|)>,\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k>|)>>
    inflate<around*|(|\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k>|)>,v|)>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`fail'>
    b|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|fail><rsub|\<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k>|)>,\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k>|)>>
    b>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
    h|)>|)>>|<cell|\<assign\>>|<cell|\<bot\>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`version'>|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|version>>>|<row|<cell|syn<around*|(|l,k,\<eta\><rsup|<maybe>><around*|(|<math-ss|`lockTime'>|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|lockTime>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>>>
  </eqnarray*>

  The <samp|case> and <samp|witness> clauses require special consideration
  which we define below. The syn function never encounters a
  <math|<math-ss|`hidden'>> node when <math|l> is well-formed except when
  <math|\<exists\>h.l<around*|[|<around*|\||l|\|>-1|]>=\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
  h|)>>, in which case the entire expression itself is hidden. These
  <math|<math-ss|`hidden'>> nodes are only used by the syncase function.

  <subsubsection|syncase>

  The syncase function constructs <samp|case> expressions as well as
  <samp|assertl> and <samp|assertr> expressions. Assertion expressions are
  produced when hidden nodes are passed as parameters. However both branches
  of a case expression cannot be hidden when <math|l> is well-formed.

  <\eqnarray*>
    <tformat|<table|<row|<cell|syncase<around*|(|l,k<rsub|0>,k<rsub|1>,\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
    h<rsub|1>|)>,k<rsub|2>,\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
    h<rsub|2>|)>|)>>|<cell|\<assign\>>|<cell|\<bot\>>>|<row|<cell|syncase<around*|(|l,k<rsub|0>,k<rsub|1>,n<rsub|1>,k<rsub|2>,\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
    h<rsub|2>|)>|)>>|<cell|\<assign\>>|<cell|<math-ss|assertl><rsub|A,B,C,\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k<rsub|0>>|)>>
    syn<around*|(|l,k<rsub|1>,n<rsub|1>|)>
    h<rsub|2><next-line><htab|5mm>where \<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k<rsub|0>>|)>=<around*|(|A+B|)>\<times\>C
    <next-line> <htab|5mm>and when \<forall\>h<rsub|1>\<point\>n<rsub|1>\<neq\>\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
    h<rsub|1>|)>>>|<row|<cell|syncase<around*|(|l,k<rsub|0>,k<rsub|1>,\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
    h<rsub|1>|)>,k<rsub|2>,n<rsub|2>|)>>|<cell|\<assign\>>|<cell|<math-ss|assertr><rsub|A,B,C,\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k<rsub|0>>|)>>
    h<rsub|1> syn<around*|(|l,k<rsub|2>,n<rsub|2>|)><next-line><htab|5mm>where
    \<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k<rsub|0>>|)>=<around*|(|A+B|)>\<times\>C
    <next-line> <htab|5mm>and when \<forall\>h<rsub|2>\<point\>n<rsub|2>\<neq\>\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
    h<rsub|2>|)>>>|<row|<cell|syncase<around*|(|l,k<rsub|0>,k<rsub|1>,n<rsub|1>,k<rsub|2>,n<rsub|2>|)>>|<cell|\<assign\>>|<cell|<math-ss|case><rsub|A,B,C,\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k<rsub|0>>|)>>
    syn<around*|(|l,k<rsub|1>,n<rsub|1>|)>
    syn<around*|(|l,k<rsub|2>,n<rsub|2>|)><next-line><htab|5mm>where
    \<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k<rsub|0>>|)>=<around*|(|A+B|)>\<times\>C
    <next-line> <htab|5mm>and when \<forall\>h<rsub|1>,h<rsub|2>\<point\>n<rsub|1>\<neq\>\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
    h<rsub|1>|)><next-line><htab|5mm>\<wedge\>n<rsub|2>\<neq\>\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
    h<rsub|2>|)>>>>>
  </eqnarray*>

  <subsubsection|inflate><label|ss:inflate>

  A <samp|`witness'> node does not hold a Simplicity value, like the
  <samp|witness> combinator requires. Instead it has a bit string that
  encodes a Simplicity value. The inflate function performs a type-directed
  decoding of this bit string to reconstruct the witness value. The inflate
  function is defined recursively via the inflation function. These two
  functions are defined below.

  <\eqnarray*>
    <tformat|<table|<row|<cell|inflation<around*|(|<1>,v|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|<around*|\<langle\>||\<rangle\>>,v|\<rangle\>>>>|<row|<cell|inflation<around*|(|A+B,0<rsub|<2>>\<blacktriangleleft\>v|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|<injl-long|A|B|a>,v<rprime|'>|\<rangle\>>*<htab|5mm>where
    <around*|\<langle\>|a,v<rprime|'>|\<rangle\>>=inflation<around*|(|A,v|)>>>|<row|<cell|inflation<around*|(|A+B,1<rsub|<2>>\<blacktriangleleft\>v|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|<injr-long|A|B|b>,v<rprime|'>|\<rangle\>>*<htab|5mm>where
    <around*|\<langle\>|b,v<rprime|'>|\<rangle\>>=inflation<around*|(|B,v|)>>>|<row|<cell|inflation<around*|(|A+B,\<epsilon\>|)>>|<cell|\<assign\>>|<cell|\<bot\>>>|<row|<cell|inflation<around*|(|A\<times\>B,v|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,v<rprime|''>|\<rangle\>>*<htab|5mm>where
    <around*|\<langle\>|a,v<rprime|'>|\<rangle\>>=inflation<around*|(|A,v|)><next-line><htab|5mm>and
    <around*|\<langle\>|b,v<rprime|''>|\<rangle\>>=inflation<around*|(|B,v<rprime|'>|)>>>>>
  </eqnarray*>

  \;

  <\eqnarray*>
    <tformat|<table|<row|<cell|inflate<around*|(|A,v|)>>|<cell|\<assign\>>|<cell|a*<htab|5mm>when
    <around*|\<langle\>|a,\<epsilon\>|\<rangle\>>=inflation<around*|(|A,v|)>>>|<row|<cell|inflate<around*|(|A,v|)>>|<cell|\<assign\>>|<cell|\<bot\><htab|5mm>otherwise>>>>
  </eqnarray*>

  As part of DoS protections and malleability protection, we want to prevent
  witness data from being inflated with unused bits. Notice that that in the
  definition of <math|syn<around*|(|k,<math-ss|`witness'> v|)>>, the inflate
  function is passed the inferred type <math|\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k>|)>>.
  Using the inferred type ensures that the witness data only contains data
  that is nominally useful by the surrounding Simplicity program.
  Furthermore, the inflate function fails unless it consumes exactly all of
  its bit string argument. This prevents <samp|`witness'> data from being
  padded with extra, unused bits.

  <section|Serialization><label|ss:Serialization>

  In this section, we define a binary prefix code for serializing Simplicity
  DAGs. Because prefix codes are self-delimiting, they provide a convenient
  framework for creating serialization formats. Compound structures can be
  serialized by concatenation of prefix codes of its substructures.

  Our serialization of Simplicity DAGs can be used as part of a network
  protocol or for writing data to a file. The program size metric (see
  Section<nbsp><inactive|<reference|<with|color|red|TODO>>>) computed for
  terms can be used to bound to the length of this binary encoding. However,
  specific binary encodings, such of this one, do not form a consensus
  critical aspect of Simplicity's design and can be substituted with other
  encodings that have similar suitable bounds.
  Appendix<nbsp><reference|app:AltSerialization> describes an alternative,
  byte-based, binary encoding.

  <subsection|Serialization of Bit Strings and Positive Numbers>

  In this section we present a recursive Elias prefix code for bit strings
  and positive natural numbers. Our code for positive natural numbers it has
  properties similar to the Elias omega coding, but is a has a simple
  recursive functional definition and some other nice properties.

  First, for any <math|n:\<bbb-N\>> with <math|0\<less\>n>, we define
  <math|<around*|\<lfloor\>|n|\<rfloor\>><rsub|<2><rsup|\<ast\>>>> to be a
  bit string for <math|n>, written in binary, with the leading
  <math|1<rsub|<2>>> chopped off.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lfloor\>|1|\<rfloor\>><rsub|<2><rsup|*\<ast\>>>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[||]>><rsub|<2>>>>|<row|<cell|<around*|\<lfloor\>|2*n|\<rfloor\>><rsub|<2><rsup|*\<ast\>>>>|<cell|\<assign\>>|<cell|<around*|\<lfloor\>|n|\<rfloor\>><rsub|<2><rsup|*\<ast\>>>\<cdummy\><verbatim|<around*|[|0|]>><rsub|<2>>>>|<row|<cell|<around*|\<lfloor\>|2*n+1|\<rfloor\>><rsub|<2><rsup|*\<ast\>>>>|<cell|\<assign\>>|<cell|<around*|\<lfloor\>|n|\<rfloor\>><rsub|<2><rsup|*\<ast\>>>\<cdummy\><verbatim|<around*|[|1|]>><rsub|<2>>>>>>
  </eqnarray*>

  For example,

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lfloor\>|1|\<rfloor\>><rsub|<2><rsup|*\<ast\>>>>|<cell|=>|<cell|<verbatim|<around*|[||]>><rsub|<2>>>>|<row|<cell|<around*|\<lfloor\>|2|\<rfloor\>><rsub|<2><rsup|*\<ast\>>>>|<cell|=>|<cell|<verbatim|<around*|[|0|]>><rsub|<2>>>>|<row|<cell|<around*|\<lfloor\>|3|\<rfloor\>><rsub|<2><rsup|*\<ast\>>>>|<cell|=>|<cell|<verbatim|<around*|[|1|]>><rsub|<2>>>>|<row|<cell|<around*|\<lfloor\>|4|\<rfloor\>><rsub|<2><rsup|*\<ast\>>>>|<cell|=>|<cell|<verbatim|<around*|[|00|]>><rsub|<2>>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>|<row|<cell|<around*|\<lfloor\>|7|\<rfloor\>><rsub|<2><rsup|*\<ast\>>>>|<cell|=>|<cell|<verbatim|<around*|[|11|]>><rsub|<2>>>>|<row|<cell|\<vdots\>>|<cell|>|<cell|\<vdots\>>>>>
  </eqnarray*>

  This binary code is not a prefix code. To make a prefix code we define
  mutually recursive function on bit strings and positive numbers. This
  encodes a bit string by prefixing it with a tag indicating if the bit
  string is null followed by the bit string's length when it is not null. It
  encodes a positive number, <math|n>, by encoding its associated bit string
  <math|<around*|\<lfloor\>|n|\<rfloor\>><rsub|<2><rsup|\<ast\>>>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<rep|\<emptyset\><rsup|<maybe>><rsub|<2><rsup|+>>|>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|0|]>><rsub|<2>>>>|<row|<cell|<rep|\<eta\><rsup|<maybe>><rsub|<2><rsup|+>><around*|(|l|)>|>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|1|]>><rsub|<2>>\<cdummy\><rep|<around*|\||l|\|>|>\<cdummy\>l>>|<row|<cell|<rep|n|>>|<cell|\<assign\>>|<cell|<rep|<around*|\<lfloor\>|n|\<rfloor\>><rsub|<2><rsup|*\<ast\>>>|>>>>>
  </eqnarray*>

  The table below illustrates this prefix code on a few inputs.

  \;

  <center|<tabular|<tformat|<cwith|1|-1|2|2|cell-halign|c>|<cwith|1|-1|4|4|cell-halign|c>|<cwith|9|9|1|-1|cell-halign|c>|<cwith|12|12|2|2|cell-halign|c>|<cwith|12|12|4|4|cell-halign|c>|<cwith|12|12|1|5|cell-halign|c>|<cwith|10|10|2|2|cell-halign|c>|<cwith|10|10|4|4|cell-halign|c>|<cwith|13|14|2|2|cell-halign|c>|<cwith|13|14|4|4|cell-halign|c>|<cwith|13|13|2|2|cell-halign|c>|<cwith|13|13|4|4|cell-halign|c>|<cwith|1|-1|1|1|cell-halign|r>|<cwith|15|15|2|2|cell-halign|c>|<cwith|15|15|4|4|cell-halign|c>|<cwith|15|15|2|2|cell-halign|c>|<cwith|15|15|4|4|cell-halign|c>|<cwith|15|15|1|5|cell-halign|c>|<cwith|15|15|1|1|cell-halign|r>|<cwith|14|14|4|4|cell-halign|c>|<cwith|14|14|4|4|cell-halign|c>|<cwith|2|2|4|4|cell-halign|c>|<cwith|3|4|4|4|cell-halign|c>|<cwith|4|4|4|4|cell-halign|c>|<cwith|5|8|4|4|cell-halign|c>|<cwith|6|6|4|4|cell-halign|c>|<cwith|7|8|4|4|cell-halign|c>|<cwith|8|8|4|4|cell-halign|c>|<cwith|10|11|4|4|cell-halign|c>|<cwith|10|11|4|4|cell-halign|c>|<cwith|10|11|4|4|cell-halign|c>|<cwith|11|11|4|4|cell-halign|c>|<cwith|13|14|4|4|cell-halign|c>|<cwith|13|14|4|4|cell-halign|c>|<cwith|13|14|4|4|cell-halign|c>|<cwith|14|14|4|4|cell-halign|c>|<cwith|13|14|2|2|cell-halign|c>|<cwith|13|14|2|2|cell-halign|c>|<cwith|13|14|2|2|cell-halign|c>|<cwith|14|14|2|2|cell-halign|c>|<cwith|7|8|2|2|cell-halign|c>|<cwith|7|8|2|2|cell-halign|c>|<cwith|7|8|2|2|cell-halign|c>|<cwith|8|8|2|2|cell-halign|c>|<cwith|5|6|2|2|cell-halign|c>|<cwith|5|6|2|2|cell-halign|c>|<cwith|5|6|2|2|cell-halign|c>|<cwith|6|6|2|2|cell-halign|c>|<cwith|3|4|2|2|cell-halign|c>|<cwith|3|4|2|2|cell-halign|c>|<cwith|3|4|2|2|cell-halign|c>|<cwith|4|4|2|2|cell-halign|c>|<cwith|1|2|2|2|cell-halign|c>|<cwith|1|2|2|2|cell-halign|c>|<cwith|1|2|2|2|cell-halign|c>|<cwith|2|2|2|2|cell-halign|c>|<cwith|10|11|2|2|cell-halign|c>|<cwith|10|11|2|2|cell-halign|c>|<cwith|10|10|2|2|cell-halign|c>|<cwith|10|11|2|2|cell-halign|c>|<cwith|10|11|2|2|cell-halign|c>|<cwith|10|11|2|2|cell-halign|c>|<cwith|11|11|2|2|cell-halign|c>|<cwith|1|-1|3|3|cell-halign|c>|<cwith|1|-1|5|5|cell-halign|l>|<table|<row|<cell|<rep|1|>>|<cell|<math|=>>|<cell|<rep|<verbatim|[]><rsub|<2>>|>>|<cell|<math|=>>|<cell|<math|<verbatim|[0]><rsub|<2>>>>>|<row|<cell|<rep|2|>>|<cell|<math|=>>|<cell|<rep|<verbatim|[0]><rsub|<2>>|>>|<cell|<math|=>>|<cell|<math|<verbatim|[100]><rsub|<2>>>>>|<row|<cell|<rep|3|>>|<cell|<math|=>>|<cell|<rep|<verbatim|[1]><rsub|<2>>|>>|<cell|<math|=>>|<cell|<math|<verbatim|[101]><rsub|<2>>>>>|<row|<cell|<rep|4|>>|<cell|<math|=>>|<cell|<rep|<verbatim|[00]><rsub|<2>>|>>|<cell|<math|=>>|<cell|<math|<verbatim|[110000]><rsub|<2>>>>>|<row|<cell|<rep|5|>>|<cell|<math|=>>|<cell|<rep|<verbatim|[01]><rsub|<2>>|>>|<cell|<math|=>>|<cell|<math|<verbatim|[110001]><rsub|<2>>>>>|<row|<cell|<rep|6|>>|<cell|<math|=>>|<cell|<rep|<verbatim|[10]><rsub|<2>>|>>|<cell|<math|=>>|<cell|<math|<verbatim|[110010]><rsub|<2>>>>>|<row|<cell|<rep|7|>>|<cell|<math|=>>|<cell|<rep|<verbatim|[11]><rsub|<2>>|>>|<cell|<math|=>>|<cell|<math|<verbatim|[110011]><rsub|<2>>>>>|<row|<cell|<rep|8|>>|<cell|<math|=>>|<cell|<rep|<verbatim|[000]><rsub|<2>>|>>|<cell|<math|=>>|<cell|<math|<verbatim|[1101000]><rsub|<2>>>>>|<row|<cell|<math|\<vdots\>>>|<cell|>|<cell|<math|\<vdots\>>>|<cell|>|<cell|<math|\<vdots\>>>>|<row|<cell|<rep|15|>>|<cell|<math|=>>|<cell|<rep|<verbatim|[111]><rsub|<2>>|>>|<cell|<math|=>>|<cell|<math|<verbatim|[1101111]><rsub|<2>>>>>|<row|<cell|<rep|16|>>|<cell|<math|=>>|<cell|<rep|<verbatim|[0000]><rsub|<2>>|>>|<cell|<math|=>>|<cell|<math|<verbatim|[11100000000]><rsub|<2>>>>>|<row|<cell|<math|\<vdots\>>>|<cell|>|<cell|<math|\<vdots\>>>|<cell|>|<cell|<math|\<vdots\>>>>|<row|<cell|<rep|<math|2<rsup|16>-1>|>>|<cell|<math|=>>|<cell|<rep|<math|<verbatim|<around|[|1|]>><rsub|<2>><rsup|15>>|>>|<cell|<math|=>>|<cell|<math|<verbatim|<around|[|11101111|]>><rsub|<2>>\<cdummy\><verbatim|<around|[|1|]>><rsub|<2>><rsup|15>>>>|<row|<rep|<math|2<rsup|16>>|>|<cell|<math|=>>|<cell|<rep|<math|<verbatim|<around|[|0|]>><rsub|<2>><rsup|16>>|>>|<cell|<math|=>>|<cell|<math|<verbatim|<around|[|111100000000|]>><rsub|<2>>\<cdummy\><verbatim|<around|[|0|]>><rsub|<2>><rsup|16>>>>|<row|<cell|<math|\<vdots\>>>|<cell|>|<cell|<math|\<vdots\>>>|<cell|>|<cell|<math|\<vdots\>>>>>>>>

  \;

  Notice that this prefix code preserves numeric ordering as lexicographical
  ordering. If <math|n> and <math|m> are positive numbers then
  <math|n\<leq\>m\<Leftrightarrow\><rep|n|>\<preceq\><rep|m|>> where
  <math|\<preceq\>> is the lexicographical ordering on bit strings. When you
  are parsing a code for a positive number that you know from context is not
  allowed to exceed some bound <math|b>. Then during parsing you can abort as
  soon as the string being parsed lexicographically exceeds <math|<rep|b|>>.
  In some cases you can abort parsing after only a few bits. For example, if
  from context you know that a the positive number must fit in a 64-bit
  integer (i.e. it is not allowed to exceed <math|2<rsup|64>-1>), then you
  can abort parsing as soon as the bit string being parsed lexicographically
  meets or exceeds the prefix <verbatim|[1111001]>.

  <subsection|Serialization of Simplicity>

  In this section we describe a fairly direct serialization for Simplicity
  DAGs. First, we provide a prefix code for <math|Node> values stripped of
  witness data:

  <\eqnarray*>
    <tformat|<table|<row|<cell|<rep|<text|<samp|`comp'>> i
    j|>>|<cell|=>|<cell|<verbatim|<around*|[|00000|]>><rsub|<2>>\<cdummy\><rep|i|>\<cdummy\><rep|j|>>>|<row|<cell|<rep|<text|<samp|`case'>>
    i j|>>|<cell|=>|<cell|<verbatim|<around*|[|00001|]>><rsub|<2>>\<cdummy\><rep|i|>\<cdummy\><rep|j|>>>|<row|<cell|<rep|<text|<samp|`pair'>>
    i j|>>|<cell|=>|<cell|<verbatim|<around*|[|00010|]>><rsub|<2>>\<cdummy\><rep|i|>\<cdummy\><rep|j|>>>|<row|<cell|<rep|<text|<samp|`disconnect'>>
    i j|>>|<cell|=>|<cell|<verbatim|<around*|[|00011|]>><rsub|<2>>\<cdummy\><rep|i|>\<cdummy\><rep|j|>>>|<row|<cell|<rep|<text|<samp|`injl'>>
    i|>>|<cell|=>|<cell|<verbatim|<around*|[|00100|]>><rsub|<2>>\<cdummy\><rep|i|>>>|<row|<cell|<rep|<text|<samp|`injr'>>
    i|>>|<cell|=>|<cell|<verbatim|<around*|[|00101|]>><rsub|<2>>\<cdummy\><rep|i|>>>|<row|<cell|<rep|<text|<samp|`take'>>
    i|>>|<cell|=>|<cell|<verbatim|<around*|[|00110|]>><rsub|<2>>\<cdummy\><rep|i|>>>|<row|<cell|<rep|<text|<samp|`drop'>>
    i|>>|<cell|=>|<cell|<verbatim|<around*|[|00111|]>><rsub|<2>>\<cdummy\><rep|i|>>>|<row|<cell|<rep|<text|<samp|`iden'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|01000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`unit'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|01001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`fail'>>
    b|>>|<cell|=>|<cell|<verbatim|<around*|[|01010|]>><rsub|<2>>\<cdummy\><around*|(|\<mu\><rsup|\<ast\>>\<circ\><around*|(|\<iota\><rsup|<2><rsup|8>><rsub|<2><rsup|\<ast\>>>|)><rsup|\<ast\>><rsup|>\<circ\>BE|)><rsup|><around*|(|b|)>>>|<row|<cell|<rep|<text|<samp|`hidden'>>
    h|>>|<cell|=>|<cell|<verbatim|<around*|[|0110|]>><rsub|<2>>\<cdummy\><around*|(|\<mu\><rsup|\<ast\>>\<circ\><around*|(|\<iota\><rsup|<2><rsup|8>><rsub|<2><rsup|\<ast\>>>|)><rsup|\<ast\>><rsup|>\<circ\>BE|)><rsup|><around*|(|h|)>>>|<row|<cell|<rep|<text|<samp|`witness'>>v|>>|<cell|=>|<cell|<verbatim|<around*|[|0111|]>><rsub|<2>>>>>>
  </eqnarray*>

  Below we give codes for Bitcoin primitive names, but each Simplicity
  application will have its own set of codes for its own primitives. The
  prefix codes for primitive names all begin with
  <math|<verbatim|[10]><rsub|<2>>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<rep|<text|<samp|`version'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`lockTime'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputsHash'>>|>>|<cell|=>|<cell|<rsub|><verbatim|<around*|[|100001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputsHash'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|100010|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`numInputs'>>|>>|<cell|=>|<verbatim|<around*|[|100011|]>><rsub|<2>>>|<row|<cell|<rep|<text|<samp|`totalnputValue'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|100100|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentPrevOutpoint'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|100101|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentValue'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|100110|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentSequence'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|100111|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentIndex'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputPrevOutpoint'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputValue'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|101001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputSequence'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|101010|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`numOutputs'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|101011|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`totalOutputValue'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|101100|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputValue'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|101101|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputScriptHash'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|101110|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`scriptCMR'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|101111|]>><rsub|<2>>>>>>
  </eqnarray*>

  <with|color|red|TODO: <verbatim|[11]> prefix reserved for jets>

  We define a <math|witnessData<around*|(|l|)> : <2><rsup|\<ast\>>> function
  for DAGs <math|l\<of\>DAG> that serializes the values held by the witness
  data:

  <\eqnarray*>
    <tformat|<table|<row|<cell|witnessDatum<around*|(|<text|<samp|`witness'>>v|)>>|<cell|\<assign\>>|<cell|v>>|<row|<cell|witnessDatum<around*|(|n|)>>|<cell|\<assign\>>|<cell|\<varepsilon\><htab|5mm><text|when>
    \<forall\>v.n\<neq\><text|<samp|`witness'>>v>>>>
  </eqnarray*>

  <\equation*>
    witnessData<around*|(|l|)>\<assign\> <rep|\<mu\><rsup|\<ast\>><around*|(|witnessDatum<rsup|*\<ast\>><around*|(|\<eta\><rsup|S><around*|(|l|)>|)>|)>|>
  </equation*>

  For serialization of DAGs, <math|l:DAG>, which is a non-empty list of
  Nodes, we have a couple of serialization options.

  <\equation*>
    stopCode<around*|(|l|)>\<assign\>\<mu\><rsup|\<ast\>><around*|(|<around*|(|\<lambda\>x.<rep|x|>|)><rsup|\<ast\>><around*|(|\<eta\><rsup|S><around*|(|l|)>|)>|)>\<cdummy\><verbatim|<around*|[|01011|]>><rsub|<2>>\<cdummy\>witnessData<around*|(|l|)>
  </equation*>

  The <math|stopCode> above serializes the list of nodes using the prefix
  code for nodes and terminating the list with the code
  <math|<verbatim|<around*|[|01011|]>><rsub|<2>>>, which has been reserved
  for use as an end-of-stream marker.

  <\equation*>
    lengthCode<around*|(|l|)>\<assign\><rep|<around*|\||l|\|>|>\<cdummy\>\<mu\><rsup|\<ast\>><around*|(|<around*|(|\<lambda\>x.<rep|x|>|)><rsup|\<ast\>><around*|(|\<eta\><rsup|S><around*|(|l|)>|)>|)>\<cdummy\>witnessData<around*|(|l|)>
  </equation*>

  The <math|lengthCode> above prefixes the serialization of DAG with the
  number of nodes, followed by the list of nodes serialized with the prefix
  code for nodes. Both <math|stopCode> and <math|lengthCode> are prefix
  codes.

  The last alternative is to directly use
  <math|\<mu\><rsup|\<ast\>><around*|(|<around*|(|\<lambda\>x.<rep|x|>|)><rsup|\<ast\>><around*|(|\<eta\><rsup|S><around*|(|l|)>|)>|)>>.
  This is suitable when, from the context of where the code is used, the
  number of nodes or the length of the code in bits is already known. This
  variant is not a prefix code.

  Which serialization format is best depends on the context in which it is
  being used. Users should choose the most suitable one for their
  application.

  Notice that the <math|witnessDatum> does not use a prefix code, and the
  witnessData simply concatenates values without separating them with
  deliminators. This works because during deserialization, type inference
  does not depend on witness data, and once type inference is complete, we
  can use the inference types of witness nodes to decode the witness values
  in sequence. In fact we could even drop the prefix-code use in the
  <math|witnessData> code itself, however we chose to put the block of all
  the witness values into a prefix-coded list so that one doesn't need to
  perform type inference to figure out where the the witness data ends.

  <subsection|Identity Merkle Root><label|ss:IMR>

  The DAG encoding for Simplicity expressions allows for sharing of
  subexpressions, however nothing in the previous section mandates sharing of
  subexpressions. \ Without manditory sharing would have a malleability
  vector where a third party could unshare every subexprssion, vastly
  inflating the weight of a transaction. \ To enforce manditory sharing we
  will introduce the notion of an identity Merkle root and require that every
  sub-DAG have a unique such identity.

  The identity Merkle root of a Simplicity expression <math|t> is defined by
  <math|<imr0|t>>. \ This value is the same as <cmr|t> except in the presence
  of <samp|witness> and <samp|disconnect> combinators which are defined as
  follows:

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|1|2|2|cell-halign|r>|<table|<row|<cell|<imr0|<math-ss|witness><rsub|A,B>
    b>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|i><rsub|<math-ss|witness>>><rsub|IV>\<comma\>
    <around*|\<langle\>|SHA256<rsub|<2>><around*|(|deflate<rsub|B><around*|(|b|)>|)>,<tmr|B>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<imr0|<math-ss|disconnect><rsub|A,B,C,D>
    s t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|SHA256<rsup|tag<rsup|i><rsub|<math-ss|disconnect>>><rsub|IV>\<comma\>
    <around*|\<langle\>|<imr0|s>,<imr0|t>|\<rangle\>>|\<rangle\>>>>>>
  </eqnarray*>

  The unique tags used are

  <\small>
    <\eqnarray*>
      <tformat|<table|<row|<cell|tag<rsup|i><rsub|<math-ss|witness>>>|<cell|\<assign\>>|<cell|<math-tt|[<SimplicityPrefix>1f4964656e746974791f7769746e657373]><rsub|2<rsup|8>>>>|<row|<cell|tag<rsup|i><rsub|<math-ss|disconnect>>>|<cell|\<assign\>>|<cell|<math-tt|[<SimplicityPrefix>1f4964656e746974791f646973636f6e6e656374]><rsub|<2><rsup|8>>>>>>
    </eqnarray*>
  </small>

  and <math|deflate<rsub|A>\<of\>A\<rightarrow\><2><rsup|\<ast\>>> is the
  inverse of <math|inflate>:

  <\eqnarray*>
    <tformat|<table|<row|<cell|deflate<rsub|<1>><around*|(|<around*|\<langle\>||\<rangle\>>|)>>|<cell|\<assign\>>|<cell|\<epsilon\><rsub|<2>>>>|<row|<cell|deflate<rsub|A+B><around*|(|<injl-long|A|B|<around*|(|a|)>>|)>>|<cell|\<assign\>>|<cell|0<rsub|<2>>\<blacktriangleleft\>deflate<rsub|A><around*|(|a|)>>>|<row|<cell|deflate<rsub|A+B><around*|(|<injr-long|A|B|<around*|(|b|)>>|)>>|<cell|\<assign\>>|<cell|1<rsub|<2>>\<blacktriangleleft\>deflate<rsub|B><around*|(|b|)>>>|<row|<cell|deflate<rsub|A\<times\>B><around*|(|<around*|\<langle\>|a,b|\<rangle\>>|)>>|<cell|\<assign\>>|<cell|deflate<rsub|A><around*|(|a|)>\<cdummy\>deflate<rsub|B><around*|(|b|)>>>>>
  </eqnarray*>

  <\lemma>
    For all <math|a\<of\>A>, <math|inflate<around*|(|A,deflate<rsub|A><around*|(|a|)>|)>=a>.
  </lemma>

  One of our anti-malleability requirements is that non-hidden nodes in a DAG
  synethesis are terms with unique identity Merkle root, input, output type
  triples. \ We also require that hidden nodes are unique.

  <\definition>
    We say a well-formed Simplicity DAG <math|l\<of\>DAG>, that has a
    substitution <math|\<varsigma\>> yielding the most general unifier for
    <math|con<around*|(|l|)>>, has maximized sharing when

    <\enumerate-numeric>
      <item>for all <math|k<rsub|1>> and <math|k<rsub|2>> such that

      <\enumerate-alpha>
        <item><math|k<rsub|1>, k<rsub|2>\<less\><around*|\||l|\|>> and

        <item><math|l<around*|[|k<rsub|1>|]>\<neq\>\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
        h<rsub|1>|)> > and <math|l<around*|[|k<rsub|2>|]>\<neq\>\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
        h<rsub|2>|)> >for any <math|h<rsub|1>> and <math|h<rsub|2>>, and

        <item><math|\<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k<rsub|1>>|)>=\<varsigma\><rsub|<1>><around*|(|\<alpha\><rsub|k<rsub|2>>|)>>
        and <math|\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k<rsub|1>>|)>=\<varsigma\><rsub|<1>><around*|(|\<beta\><rsub|k<rsub|2>>|)>>,
        and

        <item><math|<imr0|syn<around*|(|l,k<rsub|1>,l<around*|[|k<rsub|1>|]>|)>>=<imr0|syn<around*|(|l,k<rsub|2>,l<around*|[|k<rsub|2>|]>|)>>>
      </enumerate-alpha>

      then <math|k<rsub|1>=k<rsub|2>>, and

      <item>for all <math|k<rsub|1>> and <math|k<rsub|2>> such that

      <\enumerate-alpha>
        <item><math|k<rsub|1>, k<rsub|2>\<less\><around*|\||l|\|>> and

        <item><math|l<around*|[|k<rsub|1>|]>=\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
        h<rsub|>|)> > and <math|l<around*|[|k<rsub|2>|]>=\<eta\><rsup|<maybe>><around*|(|<math-ss|`hidden'>
        h|)> >for some <math|h>
      </enumerate-alpha>

      then <math|k<rsub|1>=k<rsub|2>>.
    </enumerate-numeric>
  </definition>

  <chapter|Coq Library Guide>

  The Coq development for Simplicity is found in the <verbatim|Coq/>
  directory. There are two subdirectories: <verbatim|Simplicity/> contains
  modules related to Simplicity, and the <verbatim|Util/> directory has a few
  modules dedicated to other structures that are not by themselves specific
  to Simplicity, including a short hierarchy for commutative and idempotent
  monads. We will focus on the contents of the <verbatim|Simplicity/>
  directory.

  <section|Simplicity Types>

  The Coq development for Simplicity begins with the
  <verbatim|Simplicity/Ty.v> file. This contain the inductive definition of
  <verbatim|Ty> which defines Simplicity's type expressions. The
  <verbatim|tySem> function interprets Simplicity types as Coq types, and it
  is declared as coercion. The module also provides standard arithmetic
  notation for Simplicity's sum and product types.

  The <verbatim|tyAlg> is a record collecting the operations needed to define
  structurally recursive functions for <verbatim|Ty>. These are known as
  <hlink|F-algebras|https://en.wikipedia.org/wiki/F-algebra><nbsp><cite|f-algebra>,
  and it is one of the inputs to <verbatim|tyCata> that defines catamorphisms
  from <verbatim|Ty> to another type.

  <section|Simplicity Terms>

  There are two different ways of representing of Simplicity terms defined in
  Coq. One representation is an ``initial'' representation, as an inductive
  type. The other representation is a ``final'' representation, based on
  algebras.

  Generally speaking the ``initial'' representation works well when reasoning
  about Simplicity term using induction to prove properties about them, while
  the ``final'' representation is useful for implicitly capturing shared
  sub-expressions when defining Simplicity programs.

  We begin with the ``initial'' representation, which will most readers will
  find more familiar.

  <subsection|The ``Initial'' Representation of Terms><label|ss:coqInitial>

  The <verbatim|Simplicity/Core.v> module defines an inductive family,
  <verbatim|Term A B>, for the well-typed core Simplicity language. The core
  language is the pure fragment of Simplicity that has no effects such as
  failure or read access to the transaction environment. The <verbatim|eval>
  function provides denotational semantics and interprets terms as Coq
  functions over the corresponding Coq types.

  This module also establishes the core Simplicity completeness theorem
  (Theorem<nbsp><reference|thm:CSCT>) as the
  <verbatim|Simplicity_Completeness> theorem. The proof is built from
  <verbatim|scribe>, a function to produce Simplicity terms representing
  constant functions, and <verbatim|reify> which transforms Coq functions
  over Simplicity types into Simplicity terms representing those functions.

  <subsection|The ``Final'' Representation of Terms>

  To explain the ``final'' representation of terms it is first necessary to
  understand what an algebra for Simplicity is. We can understand this by way
  of a mathematical analogy with ring theory. A ring is a mathematical
  structure consisting of a domain along with constants from that domain that
  correspond to 0 and 1, and binary functions over that domain that
  correspond to <math|\<noplus\>+> and <math|\<times\>> operations that
  satisfy certain ring laws. A term from the language of rings is an
  expression made out of <math|0>, <math|1>, <math|+>, and <math|\<times\>>.
  Given a ring and a term from the language of rings, we can interpret that
  term in the given ring and compute an element of the domain that the term
  represents. There are many different rings structures, such as the ring of
  integers, and the ring of integers modulo <math|n> for any positive number
  <math|n>. A given term can be interpreted as some value for any ring. An
  alternative way to represent terms is as a function that, given any ring,
  returns a value from its domain and does so in a ``uniform'' way. This
  would be the ``final'' representation for terms in the language of rings.

  <subsubsection|Simplicity Algebras>

  An algebra for Simplicity is an analogous structure to a ring. An algebra
  for Simplicity consists of a domain, along with constants from that domain
  that correspond to <math|<math-ss|iden>> and <math|<math-ss|unit>> and
  functions over that domain that correspond the other combinators from
  Simplicity. Unlike the case for rings, the domain of a Simplicity algebra
  is indexed by a pair of Simplicity types, and naturally the constants and
  functions that interpret Simplicity combinators must respect these types
  (and unlike rings, we are not going to impose any extra laws).

  Core Simplicity algebras are formalized in the <verbatim|Simplicity/Alg.v>
  file. The <verbatim|Core.Class.class> record captures the interpretation of
  constants and combinators for core Simplicity over a given domain. The
  <verbatim|Core.Algebra> structure is the type of Simplicity algebras,
  containing a type family for the domain, and an instance of the
  <verbatim|Core.Class.class> record for interpretations.

  Given any Simplicity algebra and a well-typed term (from the ``initial''
  representation) we can interpret that term in the algebra to get out a
  value from the domain (that has a type corresponding to the type of the
  term). The <verbatim|Core.eval> function performs this interpretation by
  recursively evaluating the interpretation of the core Simplicity
  combinators from the algebra.

  What sort of Simplicity algebras are there? The most obvious one is the
  functional semantics of Simplicity. The domain of this algebra is the
  functions between Simplicity types. This domain is indexed by the input and
  output Simplicity types. The interpretation of the <math|<math-ss|iden>>
  and <math|<math-ss|unit>> constants are the identity and constant-unit
  functions respectively and the interpretation of the other core Simplicity
  combinators is also in accordance with Simplicity's denotational semantics.
  This algebra is defined in the <verbatim|CoreSem> structure and the
  <verbatim|CorSem_correct> lemma proves that the interpretation of terms in
  the ``initial'' representation into this algebra results in the same
  function that the <verbatim|eval> function from
  <verbatim|Simplicity/Core.v> produces. The <verbatim|\|[x]\|> notation
  denotes this denotation semantics using the <verbatim|CoreSem> domain.

  Another example of a Simplicity algebra is the ``initial'' representation
  of terms themselves, which form a trivial algebra. This domain of
  Simplicity terms is also indexed by input and output Simplicity types and
  the constants and combinators are interpreted as themselves. This algebra
  is defined in the <verbatim|Core.Term> structure and the
  <verbatim|Core.eval_Term> lemma proves that the interpretation of any term
  in this algebra returns the original term back.

  There are several other Simplicity algebras. Programs for the Bit Machine
  form a Simplicity algebra with the translation from Simplicity to Bit
  Machine code defining the interpretation of core Simplicity combinators.
  Also 256-bit hashes form a Simplicity algebra with the commitment Merkle
  root computation defining the interpretation of core Simplicity
  combinators. Static analysis of resource usage for Simplicity expressions
  forms yet another set of Simplicity algebras.

  Instances of Simplicity algebras are declared as <verbatim|Canonical
  Structures>. This allows Coq's type inference engine to infer the
  interpretation of Simplicity terms when they are used in the typing
  contexts of domain of one of these Simplicity algebras.

  <subsubsection|The ``Final'' Representation>

  The ``final'' representation of a Simplicity term is as a function that
  selects a value out of any Simplicity algebra and does so in a ``uniform''
  manner. A ``uniform'' manner means a function that satisfies the
  <verbatim|Core.Parametric> property which effectively says that that the
  values chosen by the function from two domains must each be constructed
  from a composition of the interpretation of combinators in the two domains
  in the same way. In other words, the function must act the the
  interpretation of some ``initial'' represented term under
  <verbatim|Core.eval> for any domain.

  Terms in the ``initial'' representation can be converted to the ``final''
  representation by partial application of <verbatim|Core.eval>. The
  <verbatim|Core.eval_Parametric> lemma proves that the resulting ``final''
  representation resulting from <verbatim|Core.eval> satisfies the
  <verbatim|Core.Parametric> property.

  Terms in the ``final'' representation can be converted into the ``initial''
  representation by applying the function to the <verbatim|Core.Term>
  Simplicity algebra. The <verbatim|Core.eval_Term> lemma shows that
  converting from the ``initial'' representation to the ``final''
  representation and back to the ``initial'' representation returns the
  original value. The <verbatim|Core.term_eval> lemma shows that starting
  from any term in the ``final'' representation that satisfies the
  <verbatim|Core.Parametric> property and converting it to the ``initial''
  representation and back to the ``final'' representation results in an
  equivalent term. This completes the proof at the two representations are
  isomorphic.

  <subsubsection|Constructing ``Final'' Terms>

  To facilitate the construction of expression in the ``final''
  representation, the nine core combinators are defined as functions
  parameterized over all Simplicity algebras, and each combinator is proven
  to be parametric or to preserve parametericity. For the most part, these
  combinators can be used to write Simplicity expressions in the ``final''
  representation in the same way one would use constructors to write
  Simplicity expressions in the ``initial'' representation. On top of this,
  notation <verbatim|s &&& t> is defined for the pair combinator, and
  <verbatim|s \<gtr\>\<gtr\>\<gtr\> t> is defined for the composition
  combinator. Also we define the <verbatim|'H'>, <verbatim|'O'>, and
  <verbatim|'I'> notations for sequences of takes and drops over the identity
  combinator.

  For every expression built in the ``final'' representation, it is necessary
  to prove that the result satisfies the parametericity property. A
  <verbatim|parametricity> hint database is provided to facilitate automatic
  proofs of these results. Users should add their own parametricity lemmas to
  the hint database as they create new Simplicity expressions. Some examples
  of this can be found in the <verbatim|Simplicity/Arith.v> module.

  <subsection|Why two representations of Terms?>

  The ``initial'' inductive representation is the traditional definition one
  expects for terms and is easy to reason inductively about. The problem with
  this representation is that, due to lack of sharing between
  sub-expressions, it is expensive to evaluate with these terms inside Coq
  itself. For example, one cannot compute Merkle roots of anything but the
  most trivial of expressions.

  The ``final'' algebra representation solves this problem by allowing
  transparent sharing of expressions. In the ``final'' representation, terms
  are really values of a Simplicity algebra. When these values are shared
  using in Coq's let expressions, or shared via some function argument in
  Coq, those values of the algebra are shared during computation within Coq.
  This representation makes it feasible to actually compute Merkle roots for
  Simplicity expressions directly inside Coq.

  Both representations are used throughout the Simplicity Coq library. The
  isomorphism between the two representations is used to transport theorems
  between them.

  I typically use <verbatim|term : Core.Algebra> as the variable name for an
  abstract Simplicity algebra. I use this variable name because
  <verbatim|Core.Term> are the most generic type of Simplicity algebra
  (formally known as an initial algebra) so it makes sense to think of
  generic Simplicity algebras as if they are term algebras.

  <section|Example Simplicity Expressions>

  <subsection|Bits>

  The <verbatim|Simplicity/Bit.v> file defines notation for the Simplicity
  type for bits, and notation for their two values <verbatim|'Bit.zero'> and
  <verbatim|'Bit.one'>. The Simplicity expressions <verbatim|false> and
  <verbatim|true> are defined to be the constant functions that return the
  zero and one bit respectively. A few logical combinators are defined for
  bits, including the <verbatim|cond <em|thn> <em|els>> combinator which does
  case analysis on one bit of input, and executes <verbatim|<em|thn>> or
  <verbatim|<em|els>> expressions according to whether the bit represented
  true or false.

  All the combinators and Simplicity expressions are given in the ``final''
  representation and parametricity lemmas are provided.

  <subsection|Arithmetic><label|ss:coqArith>

  The <verbatim|Simplicity/Arith.v> file defines types for multi-bit words
  and defines Simplicity expressions for addition and multiplication on those
  words. <verbatim|Word <em|n>> is a Simplicity type of a
  <math|2<rsup|n>>-bit word. The <verbatim|ToZ> module defines a class of
  types of finite words. The class provides <verbatim|toZ> and
  <verbatim|fromZ> operations that convert between standard Coq integers and
  these types of finite words along with proofs that the conversion functions
  are inverses modulo the word size. <verbatim|Canonical Structure>
  declarations provide implementations for the <verbatim|Bit> and
  <verbatim|Word <em|n>> types and for pairs of of such types.

  The <verbatim|Simplicity/Arith.v> file also defines the following
  Simplicity expressions:

  <\itemize-dot>
    <item><verbatim|adder : forall n term, term (Word n * Word n) (Bit * Word
    n)>

    <item><verbatim|fullAdder : forall n term, term ((Word n * Word n) * Bit)
    (Bit * Word n)>

    <item><verbatim|multiplier : forall n term, term (Word n * Word n) (Word
    (S n))>

    <item><verbatim|fullMultiplier : forall n term,<next-line>term ((Word n *
    Word n) * (Word n * Word n)) (Word (S n))>
  </itemize-dot>

  The <verbatim|adder> expression defines the sum of two <math|2<rsup|n>>-bit
  word, returning a carry bit and a <math|2<rsup|n>>-bit word result. The
  <verbatim|fullAdder> expression defines the sum of two <math|2<rsup|n>>-bit
  word and one (carry input) bit, returning a carry bit and a
  <math|2<rsup|n>>-bit word result. The <verbatim|multiplier> expression
  defines the product of two <math|2<rsup|n>>-bit word and returns a
  <math|2<rsup|n+1>>-bit word. The <verbatim|fullMultiplier> expression takes
  a quadruple, <math|<around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,<around*|\<langle\>|c,d|\<rangle\>>|\<rangle\>>>
  of <math|2<rsup|n>>-bit words and returns <math|a\<cdot\>b+c+d> as a
  <math|2<rsup|n+1>>-bit word.

  Each of these expressions has an associated correctness lemma. These
  expressions are all defined in the ``final'' representation and there are
  parametricity lemmas for each expression.

  <subsection|SHA256>

  <section|The Hierarchy of Simplicity Language Extensions>

  <big-figure|<image|inheritance.Coq.eps||8cm||>|The inheritance hierarchy of
  algebras for Simplicity's partial extensions in
  Coq.<label|fig:inheritance>>

  So far we have only covered the algebra for the core Simplicity language in
  Coq. The various extensions to this core Simplicity language are captured
  by extensions to the record type for the core Simplicity algebra.
  Figure<nbsp><reference|fig:inheritance> illustrates the names of the
  algebras extending the <verbatim|Core> language algebra and their
  inheritance relationship. We use the ``packed-classes'' method for
  formalizing the inheritance relation of these extensions in Coq. Readers
  unfamiliar with this style should first read ``<hlink|Canonical Structures
  for the working Coq user|https://hal.inria.fr/hal-00816703v1/document>''<nbsp><cite|Mahboubi:2013>
  and ``<hlink|Packaging Mathematical Structures|https://hal.inria.fr/inria-00368403v1/document>''<nbsp><cite|garillot:2009>.

  Roughly speaking, there are two dimensions to the inheritance structure. In
  one direction, the <verbatim|Core>, <verbatim|Witness>, and
  <verbatim|Delegation> algebras all have semantics that can be interpreted
  as pure functions. That is, the function semantics of terms from these
  languages can be evaluated as functions that have no side-effects and can
  return values within any monad, including the identity monad.

  The next layer in this direction, <verbatim|Assertion>,
  <verbatim|AssertionWitness>, and <verbatim|AssertionDelegation>, extend the
  previous layer with assertion and failure expressions. These expressions
  introduce the failure effect and the functional semantics of terms from
  these languages return values within a <verbatim|MonadZero>, which includes
  the <verbatim|option> monad.

  The last layer in this direction, <verbatim|Primitive>, <verbatim|Jet>,
  <verbatim|FullSimplicity>, and <verbatim|FullSimplicityWithDelegation>,
  include primitive terms that are particular to the specific blockchain
  application. The functional semantics of terms from these language return
  values within a monad that captures the particular effects of the
  blockchain application. In the case of Bitcoin, the effects are captured by
  an environment (a.k.a reader) monad that provides read-only access to the
  signed transaction data.

  We break up the language of Simplicity into these layers because it helps
  us isolate the side-effects of the various language extensions when
  reasoning about Simplicity programs. When dealing with a sub-expression
  from the first layer, one can safely ignore the environment and failure
  effects and reason only about pure functions. Afterwards, various lemmas,
  such as <code|<code*|Simplicity.Alg.CoreSem_initial>> or
  <verbatim|Simplicity.Alg.AssertionSem_initial>, can be used to lift results
  into the monads use by the other layers when combining the pure
  sub-expression with other sub-expressions that do have effects.

  The other dimension of the inheritance structure breaks the language into
  feature sets. The <verbatim|Core>, <verbatim|Assertion>, and
  <verbatim|Primitive> algebras exclude witness and delegation features and
  encompass the set of language features that <verbatim|Jet>s are restricted
  to using. The next layer, <verbatim|Witness>, <verbatim|AssertionWitness,>
  and <verbatim|FullSimplicity>, add witness features culminating in the
  <verbatim|FullSimplcity> algebra defining the Full Simplicity language. The
  last layer, <verbatim|Delegation>, <verbatim|AssertionDelegation>, and
  <verbatim|FullSimplicityWithDelgation> provides the powerful and dangerous
  delegation extension, which should only be used with caution.

  We cover these language extensions in more detail below.

  <subsection|Witness>

  The <verbatim|Witness> algebra, found in <verbatim|Simplicity/Alg.v>,
  extends the <verbatim|Core> algebra with the <verbatim|witness> combinator.
  The <verbatim|WitnessFunSem> and <verbatim|WitnessSem> canonical structures
  define the function semantics by interpreting the terms as pure functions
  and as Kleisli morphisms for any monad, respectively. The
  <verbatim|Witness_initial> lemma relates these two interpretations.

  <subsection|Assertion>

  The <verbatim|Assertion> algebra, found in <verbatim|Simplicity/Alg.v>,
  extends the <verbatim|Core> algebra with the <verbatim|assertl>,
  <verbatim|assertr>, and <verbatim|fail> combinators. The
  <verbatim|AssertionSem> canonical structure defines the functional
  semantics of Simplicity with assertions by interpreting terms as Kleisli
  morphisms for a monad with zero. The <verbatim|AssertionSem_initial> lemma
  shows that when reasoning about the functional semantics of Simplicity with
  assertions, it suffices to reason within the <verbatim|option> monad and
  translate the result to any other monad with zero via the
  <verbatim|optionZero> homomorphism.

  The <verbatim|AssertionWitness> algebra is simply the meet of the
  <verbatim|Assertion> and <verbatim|Witness> algebras without adding any new
  combinators.

  <subsection|Delegation>

  The <verbatim|Delegation> algebra, found in
  <verbatim|Simplicity/Delegation.v>, extends the <verbatim|Witness> algebra
  with the <verbatim|disconnect> combinator. The
  <verbatim|AssertionDelegation> algebra is simply the meet of the
  <verbatim|Assertion> and <verbatim|Delegation> algebras (equiv. the meet of
  the <verbatim|AssertionWitness> and <verbatim|Delegation> algebras) without
  adding any new combinators.

  \ Building the functional semantics of Simplicity with delegation involves
  a simultaneous computation of commitment Merkle roots (see
  Section<nbsp><reference|SS:Coq:MerkleRoots>) and the functional semantics.
  To support this the <verbatim|Delegator arr A B> type is the product of the
  <verbatim|arr A B> and the <verbatim|CommitmentRoot A B> types. Whenever
  <verbatim|arr> forms an algebra from any of the previous Simplicity
  language algebras, then <verbatim|Delegator arr> is also a member of the
  same algebra. Furthermore whenever <verbatim|arr> is a Simplicity with
  witnesses algebra, then <verbatim|Delegator arr> is a Simplicity with
  witnesses and delegation algebra. Similarly whenever <verbatim|arr> is a
  Simplicity with assertions and witnesses algebra, then <verbatim|Delegator
  arr> is a Simplicity with assertions, witnesses and delegation algebra.

  The <verbatim|runDelegator> projection extracts <verbatim|arr A B>, from
  <verbatim|Delegator arr A B>. For example, <verbatim|Arrow A B> is a
  functional semantics for Simplicity with witnesses. Then, when
  <verbatim|<em|t>> is a term for Simplicity with witnesses and delegation,
  <verbatim|runDelegator t : Arrow A B> is the functional semantics of
  <verbatim|<em|t>>.

  The <verbatim|runDelegator_correctness> lemma shows that for Simplicity
  terms that don't have delegation, then <verbatim|runDelegator> returns the
  original semantics.

  <subsection|Primitives>

  The Simplicity language is parameterized by the choice of
  blockchain-specific primitives. Currently we use Coq's module system to
  capture this parameterization. A <verbatim|Module Type PrimitiveSig> found
  in <verbatim|Simplicity/Primitive.v> defines the parameters that define
  these blockchain-specific applications of simplicity:

  <\itemize>
    <item>A type family <verbatim|t : Ty -\<gtr\> Ty -\<gtr\> Set> of the
    primitive expression's syntax.

    <item>A function <verbatim|tag : forall A B, t A B -\<gtr\> hash256> that
    defines the Merkle roots for the primitives.

    <item>A type <verbatim|env : Set> that captures the relevant read-only
    context used to interpret the primitives.

    <item>A function <verbatim|sem : forall A B, t A B -\<gtr\> A -\<gtr\>
    env -\<gtr\> option B> that defines the functional semantics of the
    primitives.
  </itemize>

  At the moment, this frameworks only supports primitives that use the
  environment (and failure) side-effect; however this framework could be
  extended to allow primitives that require other effects that can be
  captured by commutative and idempotent monads (for example, the writer
  effect to a commutative and idempotent monoid).

  Given an instance of the <verbatim|PrimitiveSig>'s parameters, the
  <verbatim|PrimitiveModule> defines the algebras for the parts of the
  Simplicity language that depends on the primitives. This includes the
  <verbatim|Primitive>, <verbatim|Jet>, <verbatim|FullSimplicity> and
  <verbatim|FullSimplicityWithDelegation> algebras.

  The <verbatim|Primitive> algebra extends the <verbatim|Assertion> algebra
  with the primitives given by the <verbatim|PrimitiveSig>'s type family
  <verbatim|t> through the <verbatim|prim> combinator. The <verbatim|primSem
  M> arrow is the Kleisli arrow for the monad generated by adding an
  environment effect for the <verbatim|PrimitiveSig>'s <verbatim|env> to the
  monad <verbatim|M>. The <verbatim|PrimitivePrimSem> canonical structure
  provides the functional semantics for Simplicity with primitives by
  interpreting terms as <verbatim|primSem M> whenever <verbatim|M> is a monad
  zero.

  <subsubsection|Bitcoin>

  The <verbatim|Bitcoin> module found in <verbatim|Simplicity/Primitive/Bitcoin.v>
  provides these an instance of the <verbatim|PrimitiveSig> parameters used
  for a Bitcoin or Bitcoin-like application of Simplicity. The structures
  defining the signed transaction data are specified culminating in the
  <verbatim|sigTx> data type.

  The <verbatim|Bitcoin.prim> type lists the typed primitive expressions
  defined in Section<nbsp><reference|ss:BitcoinTransactions>. The
  <verbatim|environment> type captures the read-only context for interpreting
  these primitives and it includes a <verbatim|sigTx>, the index withing this
  transaction that is under consideration, and the commitment Merkle root of
  the script being evaluated.

  Lastly, the <verbatim|sem> function defines the functional semantics of the
  primitives in accordance with Section<nbsp><reference|ss:BTDenotationalSemantics>
  and the <verbatim|tag> function defines the Merkle roots for the primitives
  in accordance with Section<nbsp><reference|ss:BTMerkleRoots>. We use
  <verbatim|vm_compute> in the definition of <verbatim|tag> to pre-evaluate
  the definitions of the Merkle roots as an optimization.

  <subsection|Jets>

  The <verbatim|Jet> algebra, found in the <verbatim|PrimitiveModule> in
  <verbatim|Simplicity/Primtive.v>, extends the <verbatim|Primitive> algebra
  with generic support for jets. The <verbatim|jet> combinator takes a term
  <verbatim|<em|t>> from the <verbatim|Primitive> algebra and the
  <verbatim|JetPrimSem> canonical structures defines the functional semantics
  of a jet to be the functional semantics of <verbatim|<em|t>>.
  Operationally, we expect implementations of specific jets to be natively
  implemented, but this detail goes beyond the scope of the specification of
  Simplicity within Coq.

  Because <verbatim|<em|t>> is restricted to being a term from the
  <verbatim|Primitive> algebra, jets cannot contain <verbatim|witness> or
  <verbatim|disconnect> sub-expressions. While our generic definition of
  <verbatim|jets> allows any term from the <verbatim|Primitive> algebra to be
  a jet, we expect specific applications of Simplicity to limit themselves to
  a finite collection of jets through its serialization format.

  <subsection|Full Simplicity>

  The <verbatim|FullSimplicity> algebra, found in the
  <verbatim|PrimitiveModule> in <verbatim|Simplicity/Primtive.v>, is the meet
  of the <verbatim|Jet> and the <verbatim|Witness> algebras (equiv. the meet
  of the <verbatim|Jet> and <verbatim|AssertionWitness> algebras) with no
  additional combinators. It defines the full Simplicity language. The
  <verbatim|SimplicityPrimSem> canonical structure provides the functional
  semantics of the full Simplicity language as the <verbatim|primSem M> type
  family when <verbatim|M> is a monad zero.

  The <verbatim|FullSimplicityWithDelegation> algebra is the the meet of the
  <verbatim|Jet> and the <verbatim|Delegation> algebras (equiv. the meet of
  the <verbatim|FullSimplicity> and <verbatim|Delegation> algebras, or the
  meet of the <verbatim|FullSimplicity> and <verbatim|AssertionDelegation>
  algebras, etc.) defines the full Simplicity with delegation language. The
  functional semantics are defined via the
  <verbatim|SimplicityDelegationDelegator> canonical structure whose domain
  includes <verbatim|Delegator (primSem M)> when <verbatim|M> is a monad
  zero. Using <verbatim|runDelegator>, one can extract a <verbatim|primSem M>
  value as the functional semantics.

  <section|Merkle Roots><label|SS:Coq:MerkleRoots>

  The <verbatim|Simplicity/MerkleRoot.v> file defines a Merkle root of types,
  and the commitment Merkle root and annotated Merkle roots for part of the
  Simplicity language. The Merkle root of types is specified by
  <code|<code*|typeRootAlg>> and defined by <verbatim|typeRoot>. The in the
  <verbatim|CommitmentRoot A B> family the parameters are phantom parameters,
  and the value is always a <verbatim|hash256> type. Canonical Structures
  provide instances of <verbatim|CommitmentRoot> for core Simplicity, and
  Simplicity with assertions and witnesses. The <verbatim|CommitmentRoot> for
  delegation is found in <verbatim|Simplicity/Delegation.v> and the
  <verbatim|CommitmentRoot> for primitives, jets, Full Simplicity and Full
  Simplicity with delegation is found in <verbatim|Simplicity/Primtive.v>.

  These Merkle roots are computed using the SHA-256 compression function with
  unique tags providing the initial value for each language construct. These
  tags are in turn the SHA-256 hash of short (less than 56 character) ASCII
  strings. The Coq definition of SHA-256 is taken from the VST (Verified
  Software Toolchain) project<cite|Appel:2015> and the
  <verbatim|Simplicity/Digest.v> module provides an interface to that
  project.

  The VST implementation of SHA-256 is efficient enough that it is practical
  to compute some commitment Merkle roots of functions inside Coq itself
  using <verbatim|vm_compute>. See <verbatim|Fact Hash256_hashBlock> at the
  end of <verbatim|Simplicity/SHA256.v> for an example of computing the
  commitment Merkle root of a Simplicity function that computes the SHA-256
  compression function.

  <section|The Bit Machine>

  The <verbatim|Simplicity/BitMachine.v> file provides the primary definition
  of the abstract Bit Machine. This definition, and hence this file, is
  independent of the rest of the Simplicity language.

  The <verbatim|Cell> type explicitly tracks cell values in the bit machine
  as being one of <verbatim|0>, <verbatim|1>, and undefined. <verbatim|None>
  represents the undefined value and <verbatim|Some false> and <verbatim|Some
  true> represent <verbatim|0> and <verbatim|1> respectively.

  The <verbatim|ReadFrame> record represents read frames. It uses a zipper
  representation of a list with a cursor: The elements of the list in front
  of the cursor are in the <verbatim|nextData> field and the elements of the
  list behind the cursor are in the <verbatim|prevData> field stored in
  <em|reverse order>. The <verbatim|setFrame> function builds a read frame
  from a list with the cursor set to the beginning of the frame.

  The <verbatim|WriteFrame> record represents write frames. It uses a similar
  zipper representation where the <verbatim|writeData> field holds the
  elements behind the cursor in <em|reverse order>. Because write frames are
  append only, every cell in front of the cursor must be an undefined value.
  For this reason we only store the number of cells in front of the cursor in
  the <verbatim|writeEmpty> field. The <verbatim|newWriteFrame> function
  builds an empty write frame of a given size and the
  <verbatim|fullWriteFrame> function builds an filled write frame from a
  list.

  The <verbatim|RunState> record represents the non-halted states of the Bit
  Machine. It consists of

  <\itemize-dot>
    <item><verbatim|inactiveReadFrames>: a list of inactive read frames, with
    the bottom of the stack at the end of the list.

    <item><verbatim|activeReadFrame>: the active read frame, which is the top
    value of the non-empty stack of read frames.

    <item><verbatim|activeWriteFrame>: the active write frame, which is the
    top value of the non-empty stack of write frames.

    <item><verbatim|inactiveWriteFrames>: a list of inactive write frames,
    with the bottom of the stack at the end of the list.
  </itemize-dot>

  The <verbatim|State> variant is either a <verbatim|RunState> or the
  <verbatim|Halted> state and represents the possible states of the Bit
  Machine. We make the injection of <verbatim|RunState> into <verbatim|State>
  a coercion.

  It is sometimes useful to decompose the Bit Machine's state as

  <\equation*>
    <around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\><carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>*c<rsub|n<rsub|0>>>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\><cearr|c<rsub|1>*\<cdots\>*c<rsub|n<rsub|1>>><carr|?><rsup|n<rsub|2>><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>
  </equation*>

  where we are locally interested in what is immediately in front of the
  active read frame's cursor, <math|<carr|<wide*|c<rsub|1>|\<bar\>>\<cdots\>*c<rsub|n<rsub|0>>>>,
  and what is immediately surrounding the active write frame's cursor,
  <math|<cearr|c<rsub|1>*\<cdots\>*c<rsub|n<rsub|1>>><carr|?><rsup|n<rsub|2>>>.
  This is captured by the <verbatim|LocalState> type, noting that the data
  immediately surrounding the active write frame's cursor is captured by the
  <verbatim|WriteFrame> type. The remainder of the state, consisting of
  <math|<around*|[|\<Theta\>\<vartriangleright\>r<rsub|0>\<cdummy\>\<bullet\>\<cdummy\>r<rsub|0><rprime|'>\|w<rsub|0>\<cdummy\>\<bullet\>\<cdummy\><carr|?><rsup|m>\<vartriangleleft\>\<Xi\>|]>>
  is captured by the <verbatim|Context> type, which happens to be isomorphic
  to the <verbatim|RunState> type. The <verbatim|fillContext> function
  combines a <verbatim|Context> value and a <verbatim|LocalState> value to
  build a complete <verbatim|RunState> value.

  Sometimes we are interested in of some <verbatim|LocalState> within another
  <verbatim|LocalState>. The context of such a decomposition is isomorphic to
  <verbatim|LocalState> and we don't even both giving a type alias to this.
  The <verbatim|appendLocalState> function combines a context,
  <verbatim|ls1>, with a <verbatim|LocalState>, <verbatim|ls2>, to build a
  combined <verbatim|LocalState>. <verbatim|appendLocalState> makes
  <verbatim|LocalState> into a monoid and <verbatim|fillContext> becomes a
  monoid action on <verbatim|Context>s with respect to this monoid. This
  theory is not fully developed in Coq, but will be if it is needed. The
  <verbatim|context_action> lemma proves the monoid action property, which is
  the only theorem developed so far.

  The <verbatim|StateShape> type is constructed using similar fields as the
  <verbatim|State> type and contains a sequence of numbers. This is used for
  counting the number of cells in the various components of the Bit Machine's
  <verbatim|State>. The <verbatim|stateShapeSize> function tallies up the
  totals and is used later in the <verbatim|maximumMemoryResidence> function.

  <subsection|Bit Machine Code>

  The <verbatim|MachineCode.T <em|S1> <em|S2>> type enumerates the nine basic
  instructions of the Bit Machine. The type of these instructions are
  parameterized by the legal states that the instructions can successfully
  operate in, <verbatim|<em|S1>>, and the resulting state after execution of
  the instruction, <verbatim|<em|S2>>. In this way, the
  <verbatim|MachineCode.T> type family represents a precategory (also known
  as a directed multi-graph) that captures the machine instructions and their
  semantics. There is an object (a.k.a. node) for every possible state of the
  Bit Machine. There is an arrow (a.k.a. directed edge) between two states if
  there is an instruction of the Bit Machine that successfully transitions
  from the source state to the target state, and that arrow (a.k.a. directed
  edge) is labeled with the name of the instruction. The <verbatim|Abort>
  instruction is the only instruction whose final state is the
  <verbatim|Halted> state. No instruction begins from the <verbatim|Halted>
  state. The specific type <verbatim|MachineCode.T <em|S1> <em|S2>> is the
  type of all instructions that transition from state <verbatim|<em|S1>> to
  state <verbatim|<em|S2>>.

  A <dfn|thrist> of <verbatim|MachineCode.T> is the free category generated
  from the precategory <verbatim|MachineCode.T>. This free category can also
  be understood as a collection of all paths through the directed graph of
  all machine instructions and their associated state transitions. The
  specific type <verbatim|Thrst MachineCode.T <em|S1> <em|S2>> is the type of
  all sequences of instructions that transition from state <verbatim|<em|S1>>
  to state <verbatim|<em|S2>>. This type captures the semantics of sequences
  of machine instructions.

  The notation <verbatim|<em|S1> ~~\<gtr\> <em|S2>> denotes the
  <verbatim|MachineCode.T <em|S1> <em|S2>> type of single step transitions,
  which corresponds to <math|S<rsub|1>\<rightsquigarrow\>S<rsub|2>>. The
  notation <verbatim|<em|S1> -\<gtr\>\<gtr\> <em|S2>> denotes the
  <verbatim|Thrst MachineCode.T <em|S1> <em|S2>> type of multi-step
  (including 0 steps) transitions between states <verbatim|<em|S1>> and
  <verbatim|S2> and the trace of the instructions used. The
  <verbatim|runHalt> lemma proves that the only trace that begins from the
  <verbatim|Halted> state is the empty trace.

  <subsubsection|Bit Machine Programs>

  We interpret a Bit Machine <verbatim|Program> as a function taking an
  initial machine state and, if successful, returning a final machine state
  along with a thrist of machine instructions that connect the initial state
  to the final state. The notation <verbatim|S1 \<gtr\>\<gtr\>- k
  -\<gtr\>\<gtr\> S2> corresponds to <prog|S<rsub|1>|k|S<rsub|2>> and denotes
  that the program <verbatim|k> when started in state <verbatim|S1>
  successfully executes and ends in state <verbatim|S2>. The <verbatim|trace>
  function extracts a <verbatim|S1 -\<gtr\>\<gtr\> S2> trace from a program
  <verbatim|k> when <verbatim|S1 \<gtr\>\<gtr\>- k -\<gtr\>\<gtr\> S2> holds.

  For each machine instruction we use <verbatim|makeProgram> to define a
  single instruction <verbatim|Program> that tries to execute that single
  instruction once and returns that state transition. If the initial
  non-halted state given to these single instruction programs is not valid
  for their instruction, the program fails by returning <verbatim|None>.
  However, when the initial state is the <verbatim|Halted> state, the program
  succeeds but ignores its instruction and remains in the <verbatim|Halted>
  state. This corresponds to the <prog|<halted>|i|<halted>> deduction. These
  single instruction programs have an associated correctness lemma that
  proves they run successfully when run from an initial state valid for their
  instruction and a completeness lemma that proves that they were run from
  either a valid initial state or the <verbatim|Halted> state. We also define
  the trivial <verbatim|nop> program that contains no instructions and always
  succeeds.

  These single instruction (and <verbatim|nop>) programs can be combined into
  more complex programs using the <verbatim|seq> and <verbatim|choice>
  combinators. The <verbatim|seq> combinator sequences two programs, running
  the second program starting from the final state of the first program and
  combines their thrists. The sequence fails if either program fails. The
  <verbatim|choice> combinator picks between running two programs by peeking
  at the cell under the active read frame's cursor from the initial state and
  running either the first or second program depending on whether the cell
  holds a <verbatim|0> or <verbatim|1> value. When starting from a non-halted
  state, if the cell holds an undefined value, or if the active read frame's
  cursor is at the end of the frame, the <verbatim|choice> combinator fails.
  When started from the <verbatim|Halted> state, the <verbatim|choice>
  program succeeds but remains in the <verbatim|Halted> state.

  The notations <verbatim|<em|k0> ;;; <em|k1>> and <verbatim|<em|k0> \|\|\|
  <em|k1>> denote the sequence and choice combinations respectively of two
  programs and correspond to <math|k<rsub|0>;k<rsub|1>> and
  <math|k<rsub|0><around*|\|||\|>k<rsub|1>>. We also define the combinator
  <verbatim|bump <em|n> <em|k>> which corresponds to <math|n\<star\>k>.

  The <verbatim|runMachine> function takes a <verbatim|Program> and an
  initial <verbatim|State> and extracts the resulting final <verbatim|State>
  and the trace to get there, if the program is successful. For denotational
  semantics we only care about the resulting final state. For operational
  semantics we will care how we got there. A few lemmas are provided to help
  reason about the behaviour of <verbatim|runMachine> when running the
  program combinators.

  The <verbatim|maximumMemoryResidence> function computes the maximum number
  of cells used by any intermediate state from the trace of execution of a
  Bit Machine program. A few lemmas are provided to help reason about the
  behaviour of <verbatim|maximumMemoryResidence> when running the program
  combinators.

  <subsection|Translating Simplicity to the Bit Machine>

  The <verbatim|Simplicity/Translate.v> file defines how to transform
  Simplicity programs into Bit Machine programs that perform the same
  computation. The <verbatim|bitSize> and <verbatim|encode> functions
  implement <math|bitSize<around*|(|A|)>> and <math|<rep|a|A>> respectively.

  The <verbatim|Naive.translate> structure provides a Simplicity algebra for
  Bit Machine <verbatim|Progam>s that interprets Simplicity terms according
  to the naive translation. The <verbatim|Naive.translate_correct> theorem
  proves that the <verbatim|Program> generated by <verbatim|Naive.translate>
  when started from a state that contains an encoding of Simplicity
  function's input successfully ends up in a final machine state that
  contains an encoding of Simplicity function's output (and input).

  <subsection|Static Analysis>

  The <verbatim|Simplicity/StaticAnalysis.v> files defines the static
  analyses of Simplicity program that compute bounds on the various
  computational resources used by the Bit Machine when executing translated
  Simplicity. The file also proves the correctness of these upper bounds.

  The <verbatim|MaximumMemory> module defines the
  <verbatim|MaximumMemory.extraMemoryBound> algebra which is used to compute
  an upper bound on additional memory that will be used when Simplicity
  sub-expressions are naively translated to the Bit Machine and executed. The
  <verbatim|MaximumMemory.Core_spec> lemma proves that for naively translated
  core Simplicity expressions, the maximum memory used by the Bit Machine is
  the memory needed by the size of the initial state, plus the results of
  <verbatim|MaximumMemory.extraMemoryBound>. This bound holds no matter what
  the starting state is, even if it is not a valid state for holding the
  input for the Simplicity expression.

  The <verbatim|MaximumMemory.CellBound> function computes the memory used by
  the Bit Machine for evaluating Simplicity expressions starting from a
  standard initial state and <verbatim|MaximumMemory.CellBound_correct>
  proves that this upper bound is correct.

  <chapter|Haskell Library Guide>

  WARNING: None of the Haskell library development is normative. There is no
  formalized connection between any of the Haskell library and Simplicity's
  formal semantics and development in Coq. There could be errors in the
  Haskell library that cause it to disagree with the formal development
  defined in Coq. The Haskell library is intended to be used for
  experimental, exploratory and rapid development of Simplicity related work,
  but should not be relied upon for production development. For production
  development, formal developments in Coq should be created.

  The Haskell Simplicity project is split up into multiple libraries in order
  so that multiple different applications of Simplicity to different
  Blockchains can be developed and used without conflicting with each other.
  We use the Backpack feature of the Glasgow Haskell Compiler to parameterize
  and reexport common functionally for different Simplicity applications.

  <section|<verbatim|Simplicity-Core> library>

  The first library, <verbatim|Simplicity-Core>, is found in the
  <verbatim|Haskell/Core> directory. It defines the aspects of Simplicity
  that are independent of any particular Blockchain application. This include
  Simplicity's type system, Simplicity's core expression language and the
  assertions, witness, and delegation extensions, and a few other components.

  <subsection|Simplicity Types>

  The <verbatim|Core/Simplicity/Ty.hs> file contains the development of
  Simplicity types. There are three different ways that Simplicity types are
  captured in Haskell.

  The primary way Simplicity types are captured is by the <verbatim|TyC>
  class which only has instances for the Haskell types that correspond to the
  Simplicity types:

  <\itemize-dot>
    <item><verbatim|instance TyC ()>

    <item><verbatim|instance (TyC a, TyC b) =\<gtr\> TyC (Either a b)>

    <item><verbatim|instance (TyC a, TyC b) =\<gtr\> TyC (a, b)>
  </itemize-dot>

  The <verbatim|TyC> class is crafted so that its methods are not exported.
  This prevents anyone from adding further instances to the <verbatim|TyC>
  class.

  The second way Simplicity types are captured is by the <verbatim|TyReflect>
  GADT:

  <\code>
    data TyReflect a where

    \ \ OneR \ :: TyReflect ()

    \ \ SumR \ :: (TyC a, TyC b) =\<gtr\> TyReflect a -\<gtr\> TyReflect b
    -\<gtr\> TyReflect (Either a b)

    \ \ ProdR :: (TyC a, TyC b) =\<gtr\> TyReflect a -\<gtr\> TyReflect b
    -\<gtr\> TyReflect (a, b)
  </code>

  This data type provides a concrete, value-level representation of
  Simplicity types that is tied to the type-level representation of
  Simplicity types. For each Haskell type corresponding to a Simplicity type,
  <verbatim|a>, the <verbatim|TyReflect a> type has exactly one value that is
  built up out of other values of type <verbatim|TyReflect> corresponding to
  the Simplicity type sub-expression. For example the value of type
  <verbatim|TyReflect (Either () ())> is <verbatim|SumR OneR OneR>.

  The <verbatim|reify :: TyC a =\<gtr\> TyReflect a> produces the value of
  the <verbatim|TyReflect> GADT that corresponds to the type constrained by
  the <verbatim|TyC> constraint. When users have a Haskell type constrained
  by <verbatim|TyC> they can use <verbatim|reify> to get the corresponding
  concrete value of the <verbatim|TyReflect> GADT which can then be further
  processed. The <verbatim|reifyProxy> and <verbatim|reifyArrow> functions
  are helper functions for <verbatim|refiy> that let you pass types via a
  proxy.

  The third way Simplicity types are captured is by the <verbatim|Ty> type
  alias, which is the fixed point of the <verbatim|TyF> functor. This is a
  representation of Simplicity types as a data type. The <verbatim|one>,
  <verbatim|sum>, and <verbatim|prod> functions provide smart-constructors
  that handle the explicit fixed-point constructor. The <verbatim|memoCataTy>
  helps one build memoized functions that consume <verbatim|Ty> values.

  Generally speaking, we use <verbatim|TyC> to constrain Haskell types to
  Simplicity types when creating Simplicity expressions. This way Simplicity
  type errors are Haskell type errors and can be caught by the Haskell
  compiler. We use the <verbatim|Ty> type when doing computations such as
  deserializing Simplicity expressions and performing unification for
  Simplicity's type inference. The <verbatim|TyReflect> GADT links these two
  representations. For example, the <verbatim|equalTyReflect> function can
  test if two Simplicity types are equal or not, and if they are equal then
  it can unify the Haskell type variables that represent the two Simplicity
  types. The <verbatim|unreflect> function turns a <verbatim|TyReflect> value
  into a <verbatim|Ty> value by forgetting about the type parameter.

  The <verbatim|Simplicity/Ty.hs> file also defines the
  <verbatim|UntypedValue> that represents data values of Simplicity's typed,
  but in an untyped manner. This is mostly used for <samp|witness> nodes.
  There are functions to convert to and from typed and
  <verbatim|UntypedValue>s.

  Within the <verbatim|Simplicity/Ty> directory, there are modules providing
  data types that are built from Simplicity types. The
  <verbatim|Simplicity/Ty/Bit.hs> module provides a <verbatim|Bit> type,
  corresponding to <math|<2>>, and the canonical isomorphism between
  Haskell's <verbatim|Bool> type and <verbatim|Bit>.

  The <verbatim|Simplicity/Ty/Word.hs> module provides the <verbatim|Word a>
  type that describes Simplicity types for multi-bit words. Its type
  parameter is restricted to either be a single <verbatim|Bit> word type or a
  product that doubles the size of a another word type via the
  <verbatim|Vector> GADT. The <verbatim|wordSize> returns the number of bits
  a word has, or more generally the number of elements a vector has. The
  <verbatim|fromWord> and <verbatim|toWord> functions convert values of
  Simplicity words types to and from Haskell <verbatim|Integer>s (modulo the
  size of the word). The file also provides specializations of these various
  functions for word sizes between 1 and 512 bits.

  <subsection|Simplicity Terms>

  Terms are represented in tagless-final style<nbsp><cite|Carette:2009>. This
  style is analogous to the ``final'' representation of terms that is defined
  in the Coq library.

  The <verbatim|Core/Simplicity/Term/Core.hs> file develops the core
  Simplicity term language plus a few extensions. The <verbatim|Core> type
  class captures Simplicity algebras for core Simplicity expressions. Core
  Simplicity expressions are represented in Haskell by expressions of type
  <verbatim|forall a b. Core term =\<gtr\> term a b> which are expressions
  that hold for all Simplicity algebras.

  This module provides infix operators, <verbatim|(\<gtr\>\<gtr\>\<gtr\>)>
  and <verbatim|(&&&)>, for the <verbatim|comp> and <verbatim|pair>
  Simplicity combinators respectively. It also provides notation for short
  sequences of string of <samp|I>'s, <samp|O>'s and <samp|H>'s. Note that
  because <verbatim|case> is a reserved word in Haskell we use
  <verbatim|match> for Simplicity's <samp|case> combinator. Examples of
  building Simplicity expressions can be found in the next section.

  This module also provides <verbatim|Assert>, <verbatim|Witness>, and
  <verbatim|Delegate> classes for the failure, witness, and delegation
  language extensions respectively. Terms that make use of these extension
  will have these class constraints added to their type signatures. For
  example, a value of type <verbatim|forall a b. (Core term, Witness term)
  =\<gtr\> term a b> is a term in the language of Simplicity with witnesses.

  This module provides <verbatim|(-\<gtr\>)> and <verbatim|Kleisli m>
  instances of these classes that provide denotational semantics of core
  Simplicity and some extensions. For example, one can take core Simplicity
  terms and directly use them as functions. The semantics of
  <verbatim|Delegate> depends on the commitment Merkle root; you can find
  semantics for that extension in <verbatim|Indef/Simplicity/Semantics.hs>
  and it is discussed in Section<nbsp><reference|ss:DenotationalSemanticsOfFullSimplicity>.

  The primary purpose of using tagless-final style is to support transparent
  sharing of subexpressions in Simplicity. While subexpressions can be shared
  if we used a GADT to represent Simplicity terms, any recursive function
  that consumes such a GADT cannot take advantage of that sharing. Sharing
  results of static analysis between shared sub-expressions is critical to
  making static analysis practical. Adding explicit sharing to the Simplicity
  language would make the language more complex and would risk incorrectly
  implementing the sharing combinator. Explicitly building memoization tables
  could work, but will have overhead. For instance, we do this when computing
  Merkle roots of Simplicity types. However, the solution of using
  tagless-final style lets us write terms in a natural manner and we get
  sharing for Simplicity expressions at exactly the points where we have
  sharing in the Haskell representation of the term.

  <subsection|Merkle Roots>

  The <verbatim|Core/Simplicity/MerkleRoot.hs> module reexports functionality
  defined in <verbatim|Core/Simplicity/MerkleRoot/Impl.hs>, which provides
  instances of Simplicity terms that compute the commitment, identity and
  annotated Merkle roots. The <verbatim|commitmentRoot>,
  <verbatim|identityRoot>, and <verbatim|annotatedRoot> return these Merkle
  root values. The <verbatim|Simplicity/MerkleRoot.hs> module also provides a
  memoized computation of the Merkle roots for Simplicity types.

  The SHA-256 implementation is provided through an abstract interface found
  in <verbatim|Core/Simplicity/Digest.hs>, which in turn references an
  implementation of a 256-bit word type defined in
  <verbatim|Core/Simplicity/Word.hs>.

  The <verbatim|identityRoot> computation differs from <math|<imr0|t>> in
  that it additionally hashes in the input and output types of an expression
  <math|t>. This is done so that ensuring the uniqueness of the
  <math|<imr0|t>> and the input and outputs type triples can be effectively
  done by just comparing the single <verbatim|identityRoot> hash value.

  <subsection|Tensors>

  The <verbatim|Simplicity/Tensor.hs> module provides a typed
  <verbatim|Product> tensor which allows you to apply multiple
  interpretations of a Simplicity expression simultaneously. For example,
  this <verbatim|Product> is used in the <verbatim|loop> construct (see
  Section<nbsp><reference|ss:haskellLoop>) to simultaneously compute a
  commitment Merkle root alongside another interpretation.

  <subsection|Example Simplicity Expressions>

  The <verbatim|Core/Simplicity/Programs> directory contains various
  developments of Simplicity expressions in Haskell that are independent of
  any particular blockchain application.

  <subsubsection|Generic>

  The <verbatim|Core/Simplicity/Programs/Generic.hs> file provides some
  Simplicity expressions that can apply to any Simplicity type.

  The <verbatim|scribe> function produces a Simplicity expression denoting a
  constant function for any value for any Simplicity type. The <verbatim|eq>
  Simplicity expression compares any two values of the same Simplicity type
  and decides if they are equal or not.

  <subsubsection|Bits>

  The <verbatim|Core/Simplicity/Programs/Bit.hs> file has Simplicity
  expressions for bit manipulation. <verbatim|false> and <verbatim|true> are
  Simplicity expressions for the constant functions of those types and
  <verbatim|cond> provides case analysis combinator for a single bit. There
  are combinators for various logical operators. These logical operators are
  short-circuited where possible. There are also a few trinary Boolean
  Simplicity expressions that are used in hash functions such as SHA-256.

  <subsubsection|Multi-bit Words>

  The <verbatim|Core/Simplicity/Programs/Word.hs> file provides support for
  vector an multi-bit word expressions that operate on Simplicity's vector
  and word types. It provides the implementations of logical bit-vector,
  padding, truncating, shifting and rotating Simplicity expressions.

  The <verbatim|full_shift> function provides a generic shift operation that
  allows shifting in and shifting out an arbitary word size of bits. The
  <verbatim|shift_const_by> function can perform either left or right shifts,
  filling in new elements or bits with a provided value. The
  <verbatim|rotate_const> function can perform either left or right rotates
  by a constant amount.

  The <verbatim|bitwise_bin> combinator takes a Simplicity expression for a
  binary bit operation and lifts it to a Simplicity expression for a binary
  operation on arbitrary sized words that performs the bit operation
  bit-wise. There is also a variant, called <verbatim|bitwise_tri> the does
  the same thing for trinary bit operations.

  <subsubsection|Arithmetic>

  The <verbatim|Core/Simplicity/Programs/Arith.hs> file provides support for
  arithmetic and number based expressions that operate on Simplicity's word
  types interpreted as unsigned integers. It provides implementations of the
  <verbatim|zero>, <verbatim|one>, <verbatim|add>, <verbatim|subtract>,
  <verbatim|multiply>, <verbatim|divide>, and <verbatim|modulo> Simplicity
  expressions. It also provides implementations of <verbatim|lt>,
  <verbatim|le>, <verbatim|min>, <verbatim|max>, and <verbatim|median>.

  The <verbatim|eea> expression implements the extended euclidian algorithm,
  which in turn defines <verbatim|bezout>, <verbatim|cofactors>, and
  <verbatim|gcd> expressions.

  The <verbatim|absolute_value> and <verbatim|sign> expression operate on an
  intepretation of Simplicity words as signed integers (with
  <verbatim|absolute_value> returning an unsigned value).

  <subsubsection|Loop><label|ss:haskellLoop>

  The <verbatim|Core/Simplicity/Programs/Loop.hs> files is a stub module for
  holding operations for building unbounded loops via the self-delegation
  method described in Section<nbsp><reference|ss:unboundedLoop>. At the
  moment it can be used to build the <verbatim|CommitmentRoot> of an
  unbounded loop, but the code needed to redeem such a commitment has not
  been developed yet.

  <subsection|Libraries of Simplicity Expressions>

  The tagless-final style used for Simplicity expressions is designed to
  perform efficently for some interpretations of Simplicity when
  subexpressions are shared. In particular the computation of Merkle roots
  and serialization (see <reference|ss:Haskell-DAG>) are much faster to
  compute when subexpressions are shared. However the polymorphism in the
  tagless-final type used for expression is at odds with subexpression
  sharing in a naive implementation of Simplicity expressions.

  In order to realize subexpression sharing between Simplicity expressions,
  we build libraries of Simplicity expressions as a record type. We use the
  <verbatim|RecordWildcards> language extension to bring all function of a
  library in scope with a single <verbatim|Lib{..}> pattern. This approach is
  similar to ``<hlink|First-class modules without
  defaults|http://www.haskellforall.com/2012/07/first-class-modules-without-defaults.html>''
  by <hlink|Gabriel Gonzalez|https://www.blogger.com/profile/01917800488530923694>.
  Generating several Simplicity expressions together allows us to share
  common subexpressions between the different library functions all within a
  single intepretation.

  Libraries typically come with some kind of <verbatim|mkLib> function that
  given a set library dependencies, constructs an instance of the library of
  functions. Building a library from a set of dependencies allows us to share
  dependencies between different libraries when we want to use multiple
  different libraries.

  The general approach to using the libraries for your own expressions is to
  create a <verbatim|where> clause containing the <verbatim|mkLib> expression
  for all the libraries that you want to use and their dependencies that are
  bound to <verbatim|name@Lib{..}> patterns to bring all the library function
  into scope. Then you can build your expression using any of the library
  functions.

  <subsubsection|SHA-256>

  The <verbatim|Core/Simplicity/Programs/Sha256.hs> file provides a library
  of Simplicity expressions to help compute SHA-256 hashes. The <verbatim|iv>
  expression is a constant function the returns the initial value to begin a
  SHA-256 computation. The <verbatim|hashBlock> expression computes the
  SHA-256 compression function on a single block of data. To compress
  multiple blocks, multiple calls to the <verbatim|hashBlock> function can be
  chained together.

  This library has no dependencies and you can use the <verbatim|lib> library
  value directly.

  The <verbatim|Core/Simplicity/Programs/Sha256/Lib.hs> file provides an
  unpacked module version of the library. However use of this module will
  lose the subexpression sharing. Therefore this should only be used for
  testing purposes.

  <subsubsection|LibSecp256k1>

  The <verbatim|Core/Simplicity/Programs/LibSecp256k1.hs> file provides a
  library of Simplicity expressions that mimic the functional behaviour of
  the the libsecp256k1 elliptic curve library<nbsp><cite|libsecp256k1>. This
  includes Simplicity types for, and operations on secp256k1's underlying
  finite field, elliptic curve point operations in affine and Jacobian
  coordinates, and linear combinations of points.

  This module also include the <verbatim|bip0340_check> and
  <verbatim|bip0340_verify> expressions that implement Schnorr signatures as
  specified in BIP-0340<nbsp><cite|bip-0340>.

  The <verbatim|mkLib> function builds the library from the its dependency,
  the SHA-256 library. The <verbatim|lib> value illustrates how to build the
  library, but using the <verbatim|lib> value will not allow you to share the
  dependency, so it should only be used for testing purposed.

  The <verbatim|Core/Simplicity/Programs/LibSecp256k1/Lib.hs> file provides
  an unpacked module version of the library. However use of this module will
  lose the subexpression sharing. Therefore this should only be used for
  testing purposes.

  <subsubsection|CheckSigHash><label|ss:Haskell-CheckSigHash>

  The <verbatim|Core/Simplicity/Programs/CheckSigHash.hs>, while not
  technically a library, provides a <verbatim|checkSigHash> Simplicity
  program that is similiar to the <samp|CHECKSIG> operation of Bitcoin script
  except with ``Universal signature hash modes'' (see
  Section<nbsp><reference|ss:UniversalSignatureHashModes>). \ The
  <verbatim|sigHash> combinator uses <samp|disconnect> to pair the commitment
  root of a given hash mode with its output and produces the message that
  <verbatim|checkSigHash> checks its siganture against.

  <subsection|The Bit Machine>

  The <verbatim|Core/Simplicity/BitMachine/> directory has modules related to
  the Bit Machine and evaluation of Simplicity via the Bit Machine.

  The <verbatim|Core/Simplicity/BitMachine/Ty.hs> file defines
  <verbatim|bitSize>, <verbatim|padL>, and <verbatim|padR>, which define the
  <math|bitSize>, <math|padR> and <math|padL> functions from
  Section<nbsp><reference|ss:RepresentingValuesAsCellArrays>. They operate on
  the <verbatim|Ty> type. The file also defines variants of these three
  function that operate on the <verbatim|TyReflect> GADT instead.

  The <verbatim|Core/Simplicity/BitMachine.hs> file (technically not in the
  <verbatim|Core/Simplicity/BitMachine/> directory) defines the canonical
  type of a <verbatim|Cell> to be a <verbatim|Maybe Bool>, with the
  <verbatim|Nothing> value representing undefined cell values. The
  <verbatim|encode> and <verbatim|decode> functions transform a value of a
  Simplicity type to and from a list of <verbatim|Cell>s that represent the
  value. The <verbatim|executeUsing> combinator captures a common pattern of
  running a Simplicity program through an implementation of the Bit Machine
  by encoding program inputs and decoding the results. Since there is more
  than one way to compile and run Simplicity program on the Bit Machine (for
  example, see naive translation versus TCO translation), this abstraction is
  used is multiple places.

  The <verbatim|MachineCode> type alias captures canonical forms of programs
  for the Bit Machine, which is the explicit fixed point of the
  <verbatim|MachineCodeF> functor. Usually programs are built in continuation
  passing style (analogous to using difference lists to build lists), making
  use of the <verbatim|MachineCodeK> type alias. There are smart-constructors
  for each machine code that make single instruction <verbatim|MachineCodeK>
  programs. Programs are composed sequentially using ordinary function
  composition, <verbatim|(.)>. Deterministic choice between two programs is
  provided by the <verbatim|(\|\|\|)> operator. The <verbatim|nop> program is
  an alias for the identity function.

  The <verbatim|Core/Simplicity/BitMachine/Authentic.hs> file is an
  implementation of the Bit Machine that follows the formal definition of the
  Bit Machine and fully tracks undefined values. The <verbatim|Frame> type is
  used for both read frames and write frames. The <verbatim|Active> type is
  captures the pair of active read and write frames, and the <verbatim|State>
  type captures the entire state of the Bit Machine. Lenses are used to
  access the components of the State.

  The <verbatim|runMachine> function interprets <verbatim|MachineCode> in
  accordance with the semantics of the Bit Machine, and transforms an initial
  state into a final state (possibly crashing during execution). It is meant
  to be used, in conjunction with a Simplicity translator, with
  <verbatim|executeUsing>. The <verbatim|instrumentMachine> function is a
  variant of <verbatim|runMachine> that logs statistics about memory usage
  during the execution. It is used as part of the testing for static
  analysis.

  <subsubsection|Translating Simplicity to the Bit Machine>

  The <verbatim|Core/Simplicity/BitMachine/Translate.hs> file defines the
  naive translation from Simplicity to the Bit Machine. The
  <verbatim|Translation> type wraps the <verbatim|MachineCodeK> type with
  phantom type parameters in order to make an instance suitable to be a
  Simplicity algebra. The <verbatim|translate> function translates Simplicity
  terms to <verbatim|MachineCode> via the <verbatim|Translation> algebra
  (recall that a Simplicity term in tagless final form is a polymorphic value
  that can become any Simplicity algebra). The
  <verbatim|Simplicity/BitMachine/Translate/TCO.hs> file provides a similar
  <verbatim|Translation> Simplicity algebra and <verbatim|translate>
  functions, but this translating using tail composition optimization.

  \;

  <subsubsection|Static Analysis>

  The <verbatim|Core/Simplicity/BitMachine/StaticAnalysis.hs> file has
  instances to perform static analysis for bounding the maximum number of
  cells used by the Bit Machine when executing the naive translation of
  Simplicity expressions. The <verbatim|ExtraCellsBnd> type wraps the data
  needed for the static analysis with phantom type parameters in order to
  make an instance suitable for a Simplicity Algebra. The <verbatim|cellsBnd>
  function computes the bound on cell use from Simplicity terms via the
  <verbatim|ExtraCellsBnd> Algebra. The <verbatim|Core/Simplicity/BitMachine/StaticAnalysis/TCO.hs>
  file provides a similar static analysis that bounds the maximum number of
  cells used by the Bit Machine when executing the TCO translation of
  Simplicity expressions.

  The <verbatim|Core/Simplicity/BitMachine/StaticAnalysis/Tests.hs> runs a
  few of the example Simplicity expressions through the static analysis and
  compares the result with the maximum cell count of executing the Bit
  Machine on various inputs. In this file you can see an example of how
  <verbatim|executeUsing (instrumentMachine . translate) program> is used.

  <subsubsection|Fast Evaluation with FFI>

  While Simplicity with assertions expressions can be evaluated directly with
  the <verbatim|Kleisli> instance, evaluation of sophisticated expressions,
  such as Schnorr signature verification, can be extremely time and memory
  consuming. To address this the <verbatim|Core/Simplicity/FFI/Frame.hs> and
  <verbatim|Core/Simplicity/FFI/Jets.hs> files create bindings via
  <verbatim|cbits/frame.c> and <verbatim|cbits/jets.c> to the C
  implementation of jets for Simplicity with assertion expressions. The
  <verbatim|Core/Simplicity/CoreJets.hs> modules provides a
  <verbatim|fastCoreEval> that replaces evaluation of subexpressions of
  Simplicity with assertion expressions that match these jets with optimized
  implementations.

  <section|<verbatim|Simplicity-Indef> library>

  To keep the Haskell library of Simplicity modular over different blockchain
  applications we use the Glasgow Haskell Compiler's Backpack mechanism. The
  next library, <verbatim|Simplicity-Indef>, is found in the
  <verbatim|Haskell/Indef> directory. The
  <verbatim|Indef/Simplicity/Primitive.hsig> file is a module signature that
  defines the data types and functions that make up the interface that a
  blockchain application needs to provide. The remained of the
  <verbatim|Simplicity-Indef> library defines the aspects of Simplicity that
  are generic over all different Blockchain application through this
  <verbatim|Simplicity.Primitive> module signature. This includes the full
  Simplicity language, including primitives and jets, the semantics of full
  Simplicity, type inference for full Simplicity expressions, and generic
  serialization and deserialization of Simplicity expressions.

  Each different blockchain application needs to provide a module satifying
  the <verbatim|Simplicity.Primitive> signature. At the moment only the
  Bitcoin blockchain application is provided (see
  Section<nbsp><reference|ss:BitcoinPrimitives>).

  <subsection|Primitive Signature>

  The <verbatim|Indef/Simplicity/Primitive.hsig> signature provides an
  interface to the different possible primitives provided by different
  blockchain applications. This signature requires

  <\itemize>
    <item><verbatim|Prim a b>, a GADT for primitives,

    <item><verbatim|primPrefix> and <verbatim|primName> which are used to
    generate unique names for the Merkle roots of primitive expressions,

    <item><verbatim|getPrimBit>, <verbatim|putPrimBit>,
    <verbatim|getPrimByte>, <verbatim|putPrimByte>, are provide for primitive
    specific serialization and deserialization operations.

    <item><verbatim|PrimEnv> and <verbatim|primSem>, which provides the type
    of the context and the denotational semantics for evaluating primitive
    expressions.
  </itemize>

  <subsection|Primitive Terms>

  The <verbatim|Indef/Simplicity/Term.hs> module provides expressions for the
  blockchain primitives and jet extensions, in addition to re-exporting the
  <verbatim|Simplicity.Term.Core> module.

  Discounted jets are characterized by their specification, which consists of
  a Simplicity expression with assertions and primitives, but not witness nor
  delegation. <with|color|red|Later a discounted cost will be added as a
  parameter.> Be aware that universal quantifier in the <verbatim|jet>
  argument means that subexpressions within this specificaiton cannot be
  shared outside of the specification itself.

  All the Simplicity extensions are gathered together in the
  <verbatim|Simplicity> class, whose associated values of type
  <verbatim|Simplicity term =\<gtr\> term a b> are terms in the full
  Simplicity language with delegation. The semantics of full Simplicity is
  discussed in Section<nbsp><reference|ss:DenotationalSemanticsOfFullSimplicity>.

  <subsection|<verbatim|JetType> class>

  While the <verbatim|Jet> class allows any expression to be a jet, in
  reality there we will have a specific set of known jets that we have
  accelerated implements of. The <verbatim|Indef/Simplicity/JetType.hs>
  defines the <verbatim|JetType> class whose instances are types which
  represent sets of known discounted jets. The <verbatim|specification>
  method define the specification of discounted jets and the
  <verbatim|matcher> method decides if a given Simplicity expression is known
  to be substitutable by a some discounted jet. The <verbatim|implementation>
  gives an optional optimized implementation of the jet, which otherwise
  defaults to that of the <verbatim|specification>. There are also
  <verbatim|putJetBit> and <verbatim|getJetBit> used for Serialization (see
  Section<nbsp><reference|ss:Haskell-Serialization>)

  Because the set of discounted jets in use could vary over time, the
  <verbatim|JetType> class allows for different types to represent different
  sets of discounted jets. You can have a different <verbatim|JetType>
  instance for each version of the set of discounted jets.

  <subsection|Denotational Semantics of Full
  Simplicity><label|ss:DenotationalSemanticsOfFullSimplicity>

  The <verbatim|Indef/Simplicity/Term.hs> module provides an
  <verbatim|Kleisli m> instance which provides semantics for full Simplicity
  (excluding delegation), where <verbatim|m> is both a reader monad over
  <verbatim|PrimEnv> and <verbatim|MonadFail>. Semantics for the full
  Simplicity language with delegation, which depends on computing commitment
  Merkle roots, is found in the <verbatim|Indef/Simplicity/Semantics.hs>
  module.

  The <verbatim|Delegator p a b> helper type bundles a commitment Merkle root
  computation with the Simplicity semantics of <verbatim|disconnect>,
  allowing commitment Merkle roots and semantics to be evaluated
  concurrently. This allows us to create <verbatim|Delegate> and
  <verbatim|Simplicity> instances using <verbatim|Delegator>.

  The <verbatim|Semantics a b> is a of <verbatim|Delegator> for the Kleisli
  semantics that support the Blockchain primitives, and thus is an instance
  the <verbatim|Simplicity> class for expressions of full Simplicity with
  delegation. The <verbatim|sem> function defines the semantics of full
  Simplicity with delegation by returning a concrete function from
  <verbatim|PrimEnv> and <verbatim|a> to <verbatim|Maybe b>.

  The <verbatim|Indef/Simplicity/Semantics.hs> module also provides a
  <verbatim|fastEval> function that uses a <verbatim|JetType>'s optimized
  <verbatim|implementation> to evalute subexpressions with known jets.

  <subsection|Type Inference>

  The file <verbatim|Indef/Simplicity/Inference.hs> defines a concrete term
  data type for Simplicity expressions in open recursive style via the
  <verbatim|TermF ty j w> functor. The <verbatim|ty> parameter allows for
  these terms to be decorated with type annotations, though nothing in the
  data type itself enforces that the annotations are well-typed. The
  <verbatim|tyAnnotation> traversal provides access to the type annotations.
  When type annotations are unused, this <verbatim|ty> parameter is set to
  <verbatim|()>, as is the case for the <verbatim|UntypedTermF> functor
  synonym.

  The <verbatim|j> parameter determines the type of data held by
  <verbatim|Jet> nodes. This is usually of the form <verbatim|SomeArrow arr>
  for some type annotated data structure <verbatim|arr> that represents a
  type for known jets. The <verbatim|jetData> traversal provides access to
  the jet data.

  The <verbatim|w> parameter determines the type of data held by
  <verbatim|Witness> nodes. This is often <verbatim|UntypedValue>, but is
  sometimes a vector or list of <verbatim|Bool>s, which may be used in
  intermediate computations when deserializing Simplicity expressions. The
  <verbatim|witnessData> combinator is a traversal indexed by type
  annotations for accessing this <verbatim|Witness> data.

  While the fixed point of this <verbatim|TermF ty j w> functor would yield a
  type for untyped, full Simplicity terms, instead we usually use a list or
  vector of <verbatim|TermF ty j w Integer> values to build a DAG structure,
  where the <verbatim|Integer> values are references to other subexpressions
  within a list or vector. This provides a structure with explicit sharing of
  subexpressions. This structure is captured by the <verbatim|SimplicityDag>
  type synonym.

  The main functions of this module are the <verbatim|typeInference> and
  <verbatim|typeCheck> functions. The normal progression here is to first use
  the <verbatim|typeInference> function which discards the type annotations
  of the input Simplicity DAG (if any) and performs first-order unification
  to infer new, principle type annotations, with any remaining type variables
  instantiated at the <verbatim|()> type. It also adds unification
  constraints given the input and output types of the intended Simplicity
  expression provided through the <verbatim|proxy a b> argument.

  Next one would use <verbatim|traverse . witnessData> to use the inferred
  type information to decode the witness data into an
  <verbatim|UntypedValue>.

  Lastly, one would uses the <verbatim|typeCheck> function to type check the
  inferred type annotations and, if everything is successful, a proper
  well-typed Simplicity expression of is returned. Note that the one calling
  <verbatim|typeCheck> specifies the type of the resulting Simplicity
  expression; it is not inferred from the <verbatim|SimplicityDag>. The
  <verbatim|typeCheck> function should never fail after
  <verbatim|typeInference> provided the same type constraints in its proxy
  argument and the witness data has been decoded to an
  <verbatim|UntypedValue> that matches the inferred witness type.

  There are deserialization functions (see
  <reference|ss:Haskell-Serialization>) that go through this progression of
  type inference and type checking for you.

  <subsection|Serialization><label|ss:Haskell-Serialization>

  There are two main methods of serialization found in this Simplicity
  library. The primary method is serialization via a difference list of
  <verbatim|Bool>s and deserialization via a free monad representation of a
  binary branching tree. A difference list, represented within the type
  <verbatim|[Bool] -\<gtr\> [Bool]> should be familiar to most Haskell
  programmers. The same technique is used in the <verbatim|shows> function
  using the <verbatim|ShowS> type synonym and is used to avoid quadratic time
  complexity in some cases of nested appending of lists. A <verbatim|DList>
  type synonym is defined in <verbatim|Core/Simplicity/Serialization.hs>. Our
  free monad representation of binary trees is perhaps less familiar. See
  Section<nbsp><reference|ss:FreeMonadicDeserialization> for details.

  An alternative serialization method is via the <verbatim|Get> and
  <verbatim|PutM> monads from the <verbatim|cereal> package. These are used
  for serializations to and from <verbatim|ByteStrings>. The alternative
  method is deprecated and will probably be removed.

  <subsubsection|Free Monadic Deserializaiton><label|ss:FreeMonadicDeserialization>

  Our free monad representation of binary trees is perhaps less familiar. A
  binary branching tree with leaves holding values of type <verbatim|a> can
  be represented by the free monad over the functor
  <math|X\<mapsto\>X<rsup|2>>, which in Haskell could be written as
  <verbatim|Free ((-\<gtr\>) Bool) a> where <verbatim|Free> is from the
  <verbatim|Control.Monad.Free> in the <verbatim|free> package.

  \;

  <verbatim|type BinaryTree a = <verbatim|Free ((-\<gtr\>) Bool) a>>

  \;

  \ In the free monad representation the <verbatim|Pure> constructor creates
  a leaf holding an <verbatim|a> value while the <verbatim|Free> constructor
  builds a branch represented as a function <verbatim|Bool -\<gtr\>
  BinaryTree a>, which is isomorphic to a pair of binary trees.

  Given a binary tree (represented as a free monad) we can ``execute'' this
  monad to produce a value <verbatim|a> by providing an executable
  interpretation of each branch. Our interpretation of a branch is to read a
  bit from a stream of bits and recursively execute either the left branch or
  the right branch depending on whether we encounter a 0 bit or a 1 bit. This
  process repeats until we encounter a leaf, after which we halt, returning
  the value of type <verbatim|a> held by that leaf. This interpretation
  captures precisely what it means to use a prefix code to parse a stream of
  bits. Given a stream of bits we follow branches in a binary tree, left or
  right, in accordance to the bits that we encounter within the stream until
  we encounter a leaf, in which case parsing is complete and we have our
  result, plus a possible remainder of unparsed bits.

  Where does the stream of bits come from? Well, if we were to interpret this
  in the state monad, the state would hold a stream of bits. If we were to
  interpret this the <verbatim|IO> monad, we could grab a stream bits from
  <verbatim|stdin> or from a file handle. In general, we can interpret our
  free monad in any monad that offers a callback to generate bits for us to
  consume.

  \;

  <\verbatim>
    runBinaryTree : Monad m =\<gtr\> m Bool -\<gtr\> BinaryTree a -\<gtr\> m
    a

    runBinaryTree next = foldFree (\<less\>$\<gtr\> next)
  </verbatim>

  \;

  This ability to interpret a free monad within any other monad is
  essentially what it means to be a free monad in the first place.

  This free monad approach to parsing can be extended. For example, suppose
  when parsing we encounter a prefix that is not a code of any value. We can
  extend our functor to given a variant to return failure in this case. Thus
  we build a free monad over the functor <math|X\<mapsto\>1+X<rsup|2>>. In
  Haskell we could use the type <verbatim|Free (Sum (Const ()) ((-\<gtr\>)
  Bool))> for this monad or equivalently

  \;

  <\verbatim>
    type BitDecoder a = Free (Sum (Const ()) ((-\<gtr\>) Bool)) a

    \;

    runBitDecoder : Monad m =\<gtr\> m Void -\<gtr\> m Bool -\<gtr\>
    BitDecoder a -\<gtr\> m a

    runBitDecoder abort next = foldFree eta

    \ where

    \ \ eta (Inl (Const ())) = vacuous abort

    \ \ eta (Inr f) = f \<less\>$\<gtr\> next
  </verbatim>

  \;

  Our free monad interpreter now requires two callbacks. The <verbatim|next>
  callback is as before; it generates bits to be parsed. The <verbatim|abort>
  callback handles a failure case when the a sequence of bits do not
  correspond to any coded value. This callback can throw an exception or call
  <verbatim|fail>, or do whatever is appropriate in case of failure.

  This implementation of free monads suffers from a similar quadratic
  complexity issue that lists have. In some cases, nested calls to the free
  monad's bind operation can have quadratic time complexity. To mitigate this
  we choose a to use a different representation of free monads.

  The above interpreters completely characterize their corresponding free
  monads. Instead of using the <verbatim|BinaryTree a> type we can directly
  use the type <verbatim|forall m. Monad m =\<gtr\> m Bool -\<gtr\> m a>.
  Similarly we can directly use the type <verbatim|forall m. Monad m =\<gtr\>
  m Void -\<gtr\> m Bool -\<gtr\> m a> in place of the <verbatim|BitParser a>
  type <with|color|red|TODO: consider replacing <verbatim|m Void> with a
  <verbatim|MonadFail> constraint instead>. This is known as the Van
  Laarhoven free monad representation<nbsp><cite|oconnor2014> and it is what
  we use in this library.

  For example, <verbatim|getBitString> and <verbatim|getPositive> from the
  <verbatim|Simplicity.Serialization> module are decoders a list of bits and
  positive numbers respectively that use this Van Laarhoven representation of
  binary trees. Similarly <verbatim|get256Bits> from
  <verbatim|Simplicity.Digest> is a decoder for a 256-bit hash value.

  In <verbatim|Core/Simplicity/Serialization.hs> there are several adapter
  functions for executing these Van Laarhoven free monads within particular
  monads.

  <\itemize-dot>
    <item><verbatim|evalStream> evaluates a Van Laarhoven binary tree using a
    list of bits and returns <verbatim|Nothing> if all the bits are consumed
    before decoding is successful.

    <item><verbatim|evalExactVector> evaluates a Van Laarhoven binary tree
    using a vector of bits and will return <verbatim|Nothing> unless the
    vector is exactly entirely consumed.

    <item><verbatim|evalStreamWithError> evaluates a Van Laarhoven bit
    decoder using a list of bits and returns an <verbatim|Error> if the
    decoder aborts or the list runs out of bits.

    <item><verbatim|getEvalBitStream> evaluates a Van Laarhoven bit decoder
    within cereal's <verbatim|Get> monad while internally tracking partially
    consumed bytes.
  </itemize-dot>

  <subsubsection|Serialization of Simplicity DAGs><label|ss:Haskell-DAG>

  <with|font-series|bold|>The file <verbatim|Indef/Simplicity/Dag.hs>
  provides a <verbatim|jetDag> that coverts Simplicity expressions into a
  topologically sorted DAG structure with explicit sharing that is suitable
  for encoding. This conversion

  <\itemize-dot>
    <item>finds and shares identical well-typed subexpressions,

    <item>runs type inference to determine the principle type annotations
    needed to optimal sharing and pruning of unused witness data,

    <item>finds subexpressions that matches known jets and replaces them with
    <verbatim|Jet> nodes.
  </itemize-dot>

  \;

  The file <verbatim|Indef/Simplicity/Serialization/BitString.hs> provides
  <verbatim|getTermLengthCode> and <verbatim|putTermLengthCode> functions
  that decode and encode a Simplicity expression. The
  <verbatim|putTermLengthCode> function executes <verbatim|jetDag> to perform
  sharing and substitution of jets, and the <verbatim|getTermLengthCode>
  executes deserialization, type inference and type checking all together.
  The <verbatim|getTermStopCode> and <verbatim|putTermStopCode> functions
  provide the same functionality using a serialization format with a stop
  code instead of a length code prefix. The module also provides,
  <verbatim|getDagNoWitness>, <verbatim|getWitnessData> and
  <verbatim|putDag>, that are used by the <verbatim|getTerm*> and
  <verbatim|putTerm*> functions to convert between Simplicity DAGs and their
  serialized representation.

  The file <verbatim|Indef/Simplicity/Serialization/ByteString.hs> provides
  similar <verbatim|getDag> and <verbatim|putDag> functions for the
  alternative <verbatim|ByteString> encoding described in
  Appendix<nbsp><reference|app:AltSerialization>.

  <subsection|Jet Substitution>

  The <verbatim|Indef/Simplicity/Dag.hs> provides also provides a
  <verbatim|jetSubst> function uses the same substitution mechanism in found
  in Section <math|<reference|ss:Haskell-DAG>> to return a new Simplicity
  expression that replaces found jets with explicit jets. This substitution
  can change the commitment root of the overall expression and of
  subexpressions. Because the commitment root is used in the semantics of
  <verbatim|disconnect>, it is even possible for this substitution to change
  the result of evaluation of expressions.

  In order to support partial evaluation, the <verbatim|jetSubt> function
  returns a <verbatim|WrappedSimplicity> expression. This result can be
  unwrapped by the <verbatim|unwrap> function. The use of
  <verbatim|WrappedSimplicity> lets us share much of the work of substitution
  in case we want to evaluate the resulting expression with multiple
  different interpretations. Without <verbatim|WrappedSimplicity> we would
  end up needing to redo the entire subtitution for each different
  intepretation of the resulting expression.

  <section|<verbatim|Simplicity-Bitcoin> Libary><label|ss:BitcoinPrimitives>

  To instantiate the <verbatim|Simplicity-Indef> library, we need to provide
  a blockchain specific implementation of the <verbatim|Simplicity.Primitive>
  signature. The <verbatim|Simplicity-Bitcoin> library provides primitives
  used for Bitcoin applications. The <verbatim|Bitcoin/Simplicity/Bitcoin/Primitive.hs>
  module implements the <verbatim|Simplicity.Primitive> signature by
  providing the primitive expressions and their semantics for Simplicity's
  Bitcoin application. The <verbatim|Prim a b> GADT enumerates the list of
  primitive Simplicity expressions for Bitcoin. The <verbatim|PrimEnv>
  provides the context that a Simplicity expression is evaluated within,
  providing the signed transaction data, the index of the input being
  considered for redemption, and the commitment Merkle root of the Simplicity
  program itself. The <verbatim|primSem> function is an interpreter for these
  primitive expressions for the Bitcoin.

  The <verbatim|Bitcoin/Simplicity/Bitcoin/DataTypes.hs> module provides the
  data structures that make up the signed transaction data for Bitcoin.

  <section|<verbatim|Simplicity> Library>

  The <verbatim|Simplicty> library assembles all of the previous libraries
  together. The <verbatim|Simplicity-Indef> library is instantiated at all
  available implementations of the <verbatim|Simplicity.Primitive> signature,
  which at the moment is only the <verbatim|Simplicity.Bitcoin.Primitive>
  module. This Bitcoin instance of the <verbatim|Simplicity-Indef> library
  has its modules reexported under the <verbatim|Simplicity.Bitcoin> prefix.
  Specifically the following modules are reexported:

  <\itemize-dot>
    <item><verbatim|Simplicity.Term> as <verbatim|Simplicity.Bitcoin.Term>

    <item><verbatim|Simplicity.Semantics> as
    <verbatim|Simplicity.Bitcoin.Semantics>

    <item><verbatim|Simplicity.Dag> as <verbatim|Simplicity.Bitcoin.Dag<samp|>>

    <item><verbatim|Simplicity.Inference> as
    <verbatim|Simplicity.Bitcoin.Inference>

    <item><verbatim|Simplicity.Serialization.BitString> as
    <verbatim|Simplicity.Bitcoin.Serialization.BitString>

    <item><verbatim|Simplicity.Serialization.ByteString> as
    <verbatim|Simplicity.Bitcoin.Serialization.ByteString>
  </itemize-dot>

  <subsection|CheckSigHashAll>

  Some modules build on specific Simplicity blockchain applications. The
  <verbatim|Simplicity/Bitcoin/Programs/CheckSigHashAll.hs> file provides a
  library for a <verbatim|hashAll> signature hash mode for creating a Bitcoin
  specific transaction digest and a <verbatim|checkSigHashAll> Simplicity
  program that verifies Schnorr signature over that digest for a given public
  key. The <verbatim|sigHashAll> function hashes the pair of the commitment
  root of <verbatim|hashAll> with the output of <verbatim|hashAll> producing
  the message that needs to be signed. \ This signature is compatible with
  using the <verbatim|hashAll> mode with the <verbatim|checkSigHash> program
  from Section<nbsp><reference|ss:Haskell-CheckSigHash>.

  The <verbatim|Simplicity/Bitcoin/Programs/CheckSigHashAll/Lib.hs> file
  provides an unpacked module version of the library. However use of this
  module will lose the subexpression sharing. Therefore this should only be
  used for testing purposes.

  The <verbatim|Simplicity/Elements/Programs/CheckSigHashAll.hs> file
  provides similar functionality for the Elements blockchain application.

  <subsection|Known Discounted Jets>

  The <verbatim|Simplicity.Bitcoin.Jets> and
  <verbatim|Simplicity.Elements.Jets> provide a canonical <verbatim|JetType>
  of known jets. <with|color|red|Currently this only consists of
  <verbatim|CoreJets>.> These modules also provide <verbatim|getTerm*> and
  <verbatim|putTerm*> function that specifically encode and decode this set
  of jets.

  Both sets of jets draw upon the <verbatim|Simplicity.CoreJets> module which
  provides ``core'' jets that are jets that do not depend on any primitives.
  \ These ``core'' jets include

  <\itemize>
    <item>Jets for arithmetic, including 32-bit addition, subtraction and
    multiplication

    <item>Jets for hash functions, including the SHA-256 compression
    function.
  </itemize>

  These modules also reexport specialized instances of <verbatim|jetSubst>
  and <verbatim|fastEval> for their specific <verbatim|JetType>s.

  <section|Simplicity <verbatim|testsuite>>

  The <verbatim|Tests> directory has a collection of tests for a Simplicity
  <verbatim|testsuite>. The <verbatim|Tests/Tests.hs> file imports the
  various test modules to build a testing executable to run them all.

  The <verbatim|Tests/Simplicity/Programs/Tests.hs> has some QuickCheck
  properties that provide randomized testing for some of the Simplicity
  expressions developed.

  The <verbatim|Tests/Simplicity/BitMachine/Tests.hs> runs a few of the
  Simplicity expressions through the Bit Machine implementation to test that
  the value computed by the Bit Machine matches that direct interpretation of
  the same Simplicity expressions. In this file you can see an example of how
  <verbatim|executeUsing (runMachine . translate) program> is used.<chapter|C
  Library Guide>

  <appendix|Elements Application><label|app:ElementsTransactions>

  The Elements application of Simplicity is based on the Bitcoin application
  described in Section<nbsp><reference|ss:BitcoinTransactions>. The signed
  transaction data for Elements is similar to Bitcoin's but with added
  confidential amounts and assets, pegins, and asset issuances. Below we
  define the record type <math|ELEnv> defining the environment in which
  Simplicity expressions are evaluated within for the Elements application.
  <with|color|red|TODO: consider using explicit 0 amounts in place of null
  values for assetIssuanceAmounts, because explicit 0 amounts are otherwise
  invalid in transactions.>

  <\eqnarray*>
    <tformat|<table|<row|<cell|Lock>|<cell|\<assign\>>|<cell|<2><rsup|32>>>|<row|<cell|Outpoint>|<cell|\<assign\>>|<cell|<2><rsup|256>\<times\><2><rsup|32>>>|<row|<cell|Confidential>|<cell|\<assign\>
    >|<cell|PubKey>>|<row|<cell|ExplicitAsset>|<cell|\<assign\>>|<cell|<2><rsup|256>>>|<row|<cell|Asset>|<cell|\<assign\>>|<cell|Confidential+ExplicitAsset>>|<row|<cell|ExplicitAmount>|<cell|\<assign\>>|<cell|<2><rsup|64>>>|<row|<cell|Amount>|<cell|\<assign\>>|<cell|Confidential
    + ExplicitAmount>>|<row|<cell|ExplicitNonce>|<cell|\<assign\>>|<cell|<2><rsup|256>>>|<row|<cell|Nonce>|<cell|\<assign\>>|<cell|Confidential
    + ExplicitNonce>>|<row|<cell|TokenAmount>|<cell|\<assign\>>|<cell|Amount>>|<row|<cell|NewIssuance>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|contractHash\<of\><2><rsup|256>>>|<row|<cell|amounts\<of\>
    <around*|(|Amount+TokenAmount|)>+<around*|(|Amount\<times\>TokenAmount|)>>>>>>|}>>>|<row|<cell|Reissuance>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|blindingNonce\<of\>ExplicitNonce>>|<row|<cell|entropy\<of\><2><rsup|256>>>|<row|<cell|amount\<of\>
    Amount>>>>>|}>>>|<row|<cell|Issuance>|<cell|\<assign\>>|<cell|NewIssuance+Reissuance>>|<row|<cell|ElementsSigOutput>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|asset\<of\>Asset>>|<row|<cell|amount\<of\>Amount>>|<row|<cell|scriptPubKey\<of\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>>>|<row|<cell|nonce\<of\><maybe><around*|(|Nonce|)>>>>>>|}>>>|<row|<cell|ElementsUTXO>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|asset\<of\>Asset>>|<row|<cell|amount\<of\>Amount>>|<row|<cell|scriptPubKey\<of\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>>>>>>|}>>>|<row|<cell|ElementsSigInput>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|isPegin\<of\><2>>>|<row|<cell|prevOutpoint\<of\>Outpoint>>|<row|<cell|txo\<of\>ElementsUTXO
    <with|color|red|scriptPubKey is claim_script when
    isPegin>>>|<row|<cell|sequence\<of\><2><rsup|32>>>|<row|<cell|issuance:<maybe><around*|(|Issuance|)>>>>>>|}>>>|<row|<cell|ElementsSigTx>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|version\<of\><2><rsup|32>>>|<row|<cell|inputs\<of\>ElementsSigInput<rsup|+>>>|<row|<cell|outputs\<of\>ElementsSigOutput<rsup|+>>>|<row|<cell|lockTime\<of\>Lock>>>>>|}>>>|<row|<cell|ELEnv>|<cell|\<assign\>>|<cell|<around*|{|<tabular|<tformat|<table|<row|<cell|tx\<of\>ElementsSigTx>>|<row|<cell|ix\<of\><2><rsup|32>>>|<row|<cell|scriptCMR\<of\><2><rsup|256>>>>>>|}>>>>>
  </eqnarray*>

  \;

  The Elements protocol imposes limits and other constraints similar to
  Bitcoin's for transactions to be valid. We will assume that for all
  transactions the length of the <math|inputs> and <math|outputs> arrays are
  less than or equal to <math|2<rsup|25>>, and the the length of the
  scriptPubKeys lengths are also less than or equal to <math|2<rsup|25>>.
  Also we will assume that for every <math|e\<of\>ELEnv> that
  <math|<around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>\<less\><around*|\||e<around*|[|tx|]><around*|[|inputs|]>|\|>>
  so that ``current'' index being validated is, in fact, an input of the
  transaction.

  <assign|EL|<math|EL>>The monad we use for the Elements application provides
  an environment effect (also known as a reader effect) that allows
  read-access to the <math|ELEnv> value defining the Simplicity program's
  evaluation context. We call this monad <value|EL>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<EL>A>|<cell|\<assign\>>|<cell|ELEnv\<rightarrow\><maybe>A>>|<row|<cell|<EL>f<around*|(|a|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><maybe>f<around*|(|a<around*|(|e|)>|)>>>>>
  </eqnarray*>

  \;

  <EL> is a commutative, idempotent monad with zero:

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<eta\><rsup|<EL>><rsub|A><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><rsub|A><around*|(|a|)>>>|<row|<cell|\<mu\><rsup|<EL>><rsub|A><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<mu\><rsup|<maybe>><rsub|A><around*|(|<maybe><around*|(|\<lambda\>f\<point\>f<around*|(|e|)>|)><around*|(|a<around*|(|e|)>|)>|)>>>|<row|<cell|\<emptyset\><rsup|<EL>><rsub|A>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<emptyset\><rsup|<maybe>><rsub|A>>>>>
  </eqnarray*>

  \;

  We define several new primitive expressions for reading data from a
  <math|ELEnv> value. The language that uses this extension is called
  <dfn|Simplicity with Elements>.

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|version>\<of\><value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|lockTime>\<of\><value|1>\<vdash\>Lock>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputsHash>\<of\><value|1>\<vdash\><2><rsup|256>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|outputsHash>\<of\><value|1>\<vdash\><2><rsup|256>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|numInputs>\<of\><value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputIsPegin>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<2>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputPrevOutpoint>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|Outpoint|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputAsset>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|Asset|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputAmount>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|Amount|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputScriptHash>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<2><rsup|256>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputSequence>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<2><rsup|32>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputIssuanceBlinding>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<maybe><around*|(|ExplicitNonce|)>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputIssuanceContract>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<maybe><around*|(|<2><rsup|256>|)>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputIssuanceEntropy>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<maybe><around*|(|<2><rsup|256>|)>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputIssuanceAssetAmt>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<maybe><around*|(|Amount|)>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|inputIssuanceTokenAmt>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<maybe><around*|(|TokenAmount|)>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentIndex>\<of\><value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentIsPegin>\<of\><value|1>\<vdash\><2>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentPrevOutpoint>\<of\><value|1>\<vdash\>OutPoint>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentAsset>\<of\><value|1>\<vdash\>Asset>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentAmount>\<of\><value|1>\<vdash\>Amount>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentScriptHash>\<of\><value|1>\<vdash\><2><rsup|256>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentSequence>\<of\><value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentIssuanceBlinding>\<of\><value|1>\<vdash\><maybe><around*|(|ExplicitNonce|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentIssuanceContract>\<of\><value|1>\<vdash\><maybe><around*|(|<2><rsup|256>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentIssuanceEntropy>\<of\><value|1>\<vdash\><maybe><around*|(|<2><rsup|256>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentIssuanceAssetAmt>\<of\><value|1>\<vdash\><maybe><around*|(|Amount|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|currentIssuanceTokenAmt>\<of\><value|1>\<vdash\><maybe><around*|(|TokenAmount|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|numOutputs>\<of\><value|1>\<vdash\><2><rsup|32>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|outputAsset>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|Asset|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|outputAmount>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|Amount|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|outputNonce>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<maybe><around*|(|Nonce|)>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|outputScriptHash>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<2><rsup|256>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|outputNullDatum>\<of\><2><rsup|32>\<times\><2><rsup|32>\<vdash\><maybe><around*|(|<maybe><around*|(|<2><rsup|2>\<times\><2><rsup|256>+<around*|(|<2>+<2><rsup|4>|)>|)>|)>>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|totalFee>\<of\>ExplicitAsset\<vdash\>ExplicitAmount>>>>>>
  </with>

  \;

  <\with|par-mode|center>
    <tabular*|<tformat|<cwith|1|1|1|1|cell-tborder|1pt>|<table|<row|<cell|<math|<samp|scriptCMR>\<of\><value|1>\<vdash\><2><rsup|256>>>>>>>
  </with>

  <section|Denotational Semantics><label|ss:ELDenotationalSemantics>

  We extend the formal semantics of these new expressions as follows.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|version>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|e<around*|[|tx|]><around*|[|version|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|lockTime>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|e<around*|[|tx|]><around*|[|lockTime|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputsHash>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><around*|(|\<eta\><rsup|<maybe>>\<circ\>SHA256\<circ\>\<mu\><rsup|\<ast\>>\<circ\>\<eta\><rsup|S>\<circ\>inputHash<rsup|+>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|outputsHash>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><around*|(|\<eta\><rsup|<maybe>>\<circ\>SHA256\<circ\>\<mu\><rsup|\<ast\>>\<circ\>\<eta\><rsup|S>\<circ\>outputHash<rsup|+>|)><around*|(|e<around*|[|tx|]><around*|[|outputs|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|numInputs>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|\<lfloor\>|<around*|\||e<around*|[|tx|]><around*|[|inputs|]>|\|>|\<rfloor\>><rsub|32>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputIsPegin>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|isPegin|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputPrevOutpoint>>|\<rrbracket\>><rsup|<EL>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|prevOutpoint|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputAsset>>|\<rrbracket\>><rsup|EL><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|txo|]><around*|[|asset|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputAmount>>|\<rrbracket\>><rsup|EL><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|txo|]><around*|[|amount|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputScriptHash>>|\<rrbracket\>><rsup|EL><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>SHA256<around*|(|l<around*|[|txo|]><around*|[|scriptPubKey|]>|)>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputSequence>>|\<rrbracket\>><rsup|<EL>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|sequence|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputIssuanceBlinding>>|\<rrbracket\>><rsup|<EL>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\><maybe><around*|(|blindingNonce|)><around*|(|reissuance<around*|(|l|)>|)>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputIssuanceContract>>|\<rrbracket\>><rsup|<EL>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\><maybe><around*|(|contractHash|)><around*|(|newIssuance<around*|(|l|)>|)>|)><next-line><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputIssuanceEntropy>>|\<rrbracket\>><rsup|<EL>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\><maybe><around*|(|entropy|)><around*|(|reissuance<around*|(|l|)>|)>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputIssuanceAssetAmt>>|\<rrbracket\>><rsup|<EL>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|issuanceAssetAmt|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|inputIssuanceTokenAmt>>|\<rrbracket\>><rsup|<EL>><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|issuanceTokenAmt|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentIndex>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|e<around*|[|ix|]>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentIsPegin>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><maybe><around*|(|\<lambda\>l\<point\>l<around*|[|isPegin|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentPrevOutpoint>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><maybe><around*|(|\<lambda\>l\<point\>l<around*|[|prevOutpoint|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentAsset>>|\<rrbracket\>><rsup|EL><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><maybe><around*|(|\<lambda\>l\<point\>l<around*|[|txo|]><around*|[|asset|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentAmount>>|\<rrbracket\>><rsup|EL><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><maybe><around*|(|\<lambda\>l\<point\>l<around*|[|txo|]><around*|[|amount|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentScriptHash>>|\<rrbracket\>><rsup|EL><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><maybe><around*|(|\<lambda\>l\<point\>SHA256<around*|(|l<around*|[|txo|]><around*|[|scriptPubKey|]>|)>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentSequence>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><maybe><around*|(|\<lambda\>l\<point\>l<around*|[|sequence|]>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentIssuanceBlinding>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><maybe><around*|(|\<lambda\>l\<point\><maybe><around*|(|blindingNonce|)><around*|(|reissuance<around*|(|l|)>|)>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentIssuanceContract>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><maybe><around*|(|\<lambda\>l\<point\><maybe><around*|(|contractHash|)><around*|(|newIssuance<around*|(|l|)>|)>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentIssuanceEntropy>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><maybe><around*|(|\<lambda\>l\<point\><maybe><around*|(|entropy|)><around*|(|reissuance<around*|(|l|)>|)>|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentIssuanceAssetAmt>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><maybe><around*|(|issuanceAssetAmt|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|currentIssuanceTokenAmt>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\><maybe><around*|(|issuanceTokenAmt|)><around*|(|e<around*|[|tx|]><around*|[|inputs|]><around*|\<lceil\>|e<around*|[|ix|]>|\<rceil\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|numOutputs>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|\<lfloor\>|<around*|\||e<around*|[|tx|]><around*|[|outputs|]>|\|>|\<rfloor\>><rsub|32>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|outputAsset>>|\<rrbracket\>><rsup|EL><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|asset|]>|)><around*|(|e<around*|[|tx|]><around*|[|outputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|outputAmount>>|\<rrbracket\>><rsup|EL><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>l<around*|[|amount|]>|)><around*|(|e<around*|[|tx|]><around*|[|outputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|outputScriptHash>>|\<rrbracket\>><rsup|EL><around*|(|i|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>SHA256<around*|(|l<around*|[|scriptPubKey|]>|)>|)><around*|(|e<around*|[|tx|]><around*|[|outputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|outputNullDatum>>|\<rrbracket\>><rsup|EL><around*|\<langle\>|i,j|\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|\<mu\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>l\<point\>nullDatum<around*|\<langle\>|l<around*|[|scriptPubKey|]>,<around*|\<lceil\>|j|\<rceil\>>|\<rangle\>>|)>|)><next-line><around*|(|e<around*|[|tx|]><around*|[|outputs|]><around*|\<lceil\>|i|\<rceil\>>|)>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|totalFee>>|\<rrbracket\>><rsup|<EL>><around*|(|a|)>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|fee<around*|\<langle\>|e<around*|[|tx|]><around*|[|outputs|]>,a|\<rangle\>>|)>>>|<row|<cell|<around*|\<llbracket\>|<math-ss|<math|scriptCMR>>|\<rrbracket\>><rsup|<EL>><around*|\<langle\>||\<rangle\>>>|<cell|\<assign\>>|<cell|\<lambda\>e\<of\>ELEnv\<point\>\<eta\><rsup|<maybe>><around*|(|e<around*|[|scriptCMR|]>|)>>>>>
  </eqnarray*>

  where

  <\eqnarray*>
    <tformat|<table|<row|<cell|isNewIssuance<around*|(|\<eta\><rsup|S><around*|(|<injl|<around*|(|l|)>>|)>|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|S><around*|(|l|)>>>|<row|<cell|isNewIssuance<around*|(|\<eta\><rsup|S><around*|(|<injr|<around*|(|r|)>>|)>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>>>>|<row|<cell|isNewIssuance<around*|(|\<emptyset\><rsup|<maybe>>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>>>>|<row|<cell|isReissuance<around*|(|\<eta\><rsup|S><around*|(|<injl|<around*|(|l|)>>|)>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>>>>|<row|<cell|isReissuance<around*|(|\<eta\><rsup|S><around*|(|<injr|<around*|(|r|)>>|)>|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|S><around*|(|r|)>>>|<row|<cell|isReissuance<around*|(|\<emptyset\><rsup|<maybe>>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>>>>|<row|<cell|newIssuance<around*|(|l|)>>|<cell|\<assign\>>|<cell|isNewIssuance<around*|(|l<around*|[|issuance|]>|)>>>|<row|<cell|reissuance<around*|(|l|)>>|<cell|\<assign\>>|<cell|isReissuance<around*|(|l<around*|[|issuance|]>|)>>>|<row|<cell|hasAssetAmt<around*|(|<injl|<around*|(|<injl|<around*|(|a|)>>|)>>|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|<maybe>><around*|(|a|)>>>|<row|<cell|hasAssetAmt<around*|(|<injl|<around*|(|<injr|<around*|(|t|)>>|)>>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>>>>|<row|<cell|hasAssetAmt<around*|(|<injr|<around*|\<langle\>|a,t|\<rangle\>>>|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|<maybe>><around*|(|a|)>>>|<row|<cell|hasTokenAmt<around*|(|<injl|<around*|(|<injl|<around*|(|a|)>>|)>>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>>>>|<row|<cell|hasTokenAmt<around*|(|<injl|<around*|(|<injr|<around*|(|t|)>>|)>>|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|<maybe>><around*|(|t|)>>>|<row|<cell|hasTokenAmt<around*|(|<injr|<around*|\<langle\>|a,t|\<rangle\>>>|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|<maybe>><around*|(|t|)>>>|<row|<cell|hasIssuanceAssetAmt<around*|(|\<eta\><rsup|S><around*|(|<injl|<around*|(|l|)>>|)>|)>>|<cell|\<assign\>>|<cell|hasAssetAmt<around*|(|l<around*|[|amounts|]>|)>>>|<row|<cell|hasIssuanceAssetAmt<around*|(|\<eta\><rsup|S><around*|(|<injr|<around*|(|r|)>>|)>|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|<maybe>><around*|(|r<around*|[|amount|]>|)>>>|<row|<cell|hasIssuanceAssetAmt<around*|(|\<emptyset\><rsup|<maybe>>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>>>>|<row|<cell|hasIssuanceTokenAmt<around*|(|\<eta\><rsup|S><around*|(|<injl|<around*|(|l|)>>|)>|)>>|<cell|\<assign\>>|<cell|hasTokenAmt<around*|(|l<around*|[|amounts|]>|)>>>|<row|<cell|hasIssuanceTokenAmt<around*|(|\<eta\><rsup|S><around*|(|<injr|<around*|(|r|)>>|)>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>>>>|<row|<cell|hasIssuanceTokenAmt<around*|(|\<emptyset\><rsup|<maybe>>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>>>>|<row|<cell|issuanceAssetAmt<around*|(|l|)>>|<cell|\<assign\>>|<cell|hasIssuanceAssetAmt<around*|(|l<around*|[|issuance|]>|)>>>|<row|<cell|issuanceTokenAmt<around*|(|l|)>>|<cell|\<assign\>>|<cell|hasIssuanceTokenAmt<around*|(|l<around*|[|issuance|]>|)>>>|<row|<cell|fee<around*|\<langle\>|\<epsilon\>,a|\<rangle\>>>|<cell|\<assign\>>|<cell|<around*|\<lfloor\>|0|\<rfloor\>><rsub|64>>>|<row|<cell|fee<around*|\<langle\>|o\<blacktriangleleft\>l,a|\<rangle\>>>|<cell|\<assign\>>|<cell|fee<around*|\<langle\>|l,a|\<rangle\>><op|<around*|\<lfloor\>|+|\<rfloor\>><rsub|64>>
    v<htab|5mm>when o<around*|[|asset|]>=<injr|<around*|(|a|)>><next-line><htab|5mm>and
    o<around*|[|value|]>=<injr|<around*|(|v|)>><next-line><htab|5mm>and
    o<around*|[|scriptPubKey|]>=\<epsilon\>>>|<row|<cell|fee<around*|\<langle\>|o\<blacktriangleleft\>l,a|\<rangle\>>>|<cell|\<assign\>>|<cell|fee<around*|\<langle\>|l,a|\<rangle\>><htab|5mm>when
    o<around*|[|asset|]>\<neq\><injr|<around*|(|a|)>><next-line><htab|5mm>or
    \<forall\>v\<point\>o<around*|[|value|]>\<neq\><injr|<around*|(|v|)>><next-line><htab|5mm>or
    o<around*|[|scriptPubKey|]>\<neq\>\<epsilon\>>>|<row|<cell|encAsset<around*|(|\<emptyset\><rsup|<maybe>>|)>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|<math-tt|00>|]>><rsub|<2><rsup|8>>>>|<row|<cell|encAsset<around*|(|\<eta\><rsup|<maybe>><around*|(|<injr|<around*|(|a|)>>|)>|)>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|<math-tt|01>|]>><rsub|<2><rsup|8>>\<cdummy\>BE<rsub|256><around*|(|a|)>>>|<row|<cell|encAsset<around*|(|\<eta\><rsup|<maybe>><around*|(|<injl|<around*|\<langle\>|<math-tt|0><rsub|<2>>,x|\<rangle\>>>|)>|)>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|<math-tt|0a>|]>><rsub|<2><rsup|8>>\<cdummy\>BE<rsub|256><around*|(|x|)>>>|<row|<cell|encAsset<around*|(|\<eta\><rsup|<maybe>><around*|(|<injl|<around*|\<langle\>|<math-tt|1><rsub|<2>>,x|\<rangle\>>>|)>|)>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|<math-tt|0b>|]>><rsub|<2><rsup|8>>\<cdummy\>BE<rsub|256><around*|(|x|)>>>|<row|<cell|encAmt<around*|(|\<emptyset\><rsup|<maybe>>|)>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|<math-tt|00>|]>><rsub|<2><rsup|8>>>>|<row|<cell|encAmt<around*|(|\<eta\><rsup|<maybe>><around*|(|<injr|<around*|(|v|)>>|)>|)>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|<math-tt|01>|]>><rsub|<2><rsup|8>>\<cdummy\>BE<rsub|64><around*|(|v|)>>>|<row|<cell|encAmt<around*|(|\<eta\><rsup|<maybe>><around*|(|<injl|<around*|\<langle\>|<math-tt|0><rsub|<2>>,x|\<rangle\>>>|)>|)>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|<math-tt|08>|]>><rsub|<2><rsup|8>>\<cdummy\>BE<rsub|256><around*|(|x|)>>>|<row|<cell|encAmtt<around*|(|\<eta\><rsup|<maybe>><around*|(|<injl|<around*|\<langle\>|<math-tt|1><rsub|<2>>,x|\<rangle\>>>|)>|)>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|<math-tt|09>|]>><rsub|<2><rsup|8>>\<cdummy\>BE<rsub|256><around*|(|x|)>>>|<row|<cell|encNonce<around*|(|\<emptyset\><rsup|<maybe>>|)>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|<math-tt|00>|]>><rsub|<2><rsup|8>>>>|<row|<cell|encNonce<around*|(|\<eta\><rsup|<maybe>><around*|(|<injr|<around*|(|a|)>>|)>|)>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|<math-tt|01>|]>><rsub|<2><rsup|8>>\<cdummy\>BE<rsub|256><around*|(|a|)>>>|<row|<cell|encNonce<around*|(|\<eta\><rsup|<maybe>><around*|(|<injl|<around*|\<langle\>|<math-tt|0><rsub|<2>>,x|\<rangle\>>>|)>|)>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|<math-tt|02>|]>><rsub|<2><rsup|8>>\<cdummy\>BE<rsub|256><around*|(|x|)>>>|<row|<cell|encNonce<around*|(|\<eta\><rsup|<maybe>><around*|(|<injl|<around*|\<langle\>|<math-tt|1><rsub|<2>>,x|\<rangle\>>>|)>|)>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|<math-tt|03>|]>><rsub|<2><rsup|8>>\<cdummy\>BE<rsub|256><around*|(|x|)>>>|<row|<cell|encIssuance<around*|(|\<emptyset\><rsup|<maybe>>|)>>|<cell|\<assign\>>|<cell|<verbatim|<around*|[|<math-tt|00>|]>><rsub|<2><rsup|8>>\<cdummy\><verbatim|<around*|[|<math-tt|00>|]>><rsub|<2><rsup|8>>>>|<row|<cell|encIssuance<around*|(|\<eta\><rsup|<maybe>><around*|(|<injl|<around*|(|x|)>>|)>|)>>|<cell|\<assign\>>|<cell|encAmt<around*|(|hasAssetAmt<around*|(|x<around*|[|amounts|]>|)>|)>\<cdummy\><next-line>encAmt<around*|(|hasTokenAmt<around*|(|x<around*|[|amounts|]>|)>|)>\<cdummy\><next-line>BE<rsub|256><around*|(|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>|)>\<cdummy\><next-line>BE<rsub|256><around*|(|x<around*|[|contractHash|]>|)>>>|<row|<cell|encIssuance<around*|(|\<eta\><rsup|<maybe>><around*|(|<injr|<around*|(|x|)>>|)>|)>>|<cell|\<assign\>>|<cell|encAmt<around*|(|\<eta\><rsup|S><around*|(|x<around*|[|amount|]>|)>|)>\<cdummy\><next-line>encAmt<around*|(|\<emptyset\><rsup|<maybe>>|)>\<cdummy\><next-line>BE<rsub|256><around*|(|x<around*|[|blindingNonce|]>|)>\<cdummy\><next-line>BE<rsub|256><around*|(|x<around*|[|entropy|]>|)>>>>>
  </eqnarray*>

  and

  <\eqnarray*>
    <tformat|<table|<row|<cell|inputHash<around*|(|l|)>>|<cell|\<assign\>>|<cell|BE<rsub|256><around*|(|\<pi\><rsub|1><around*|(|l<around*|[|prevOutpoint|]>|)>|)>\<cdummy\>LE<rsub|32><around*|(|\<pi\><rsub|2><around*|(|l<around*|[|prevOutpoint|]>|)>|)>\<cdummy\>LE<rsub|32><around*|(|l<around*|[|sequence|]>|)>\<cdummy\><next-line>encIssuance<around*|(|l<around*|[|issuance|]>|)>>>|<row|<cell|ouputHash<around*|(|l|)>>|<cell|\<assign\>>|<cell|encAsset<around*|(|\<eta\><rsup|<maybe>><around*|(|l<around*|[|asset|]>|)>|)>\<cdummy\>encAmt<around*|(|\<eta\><rsup|<maybe>><around*|(|l<around*|[|amount|]>|)>|)>\<cdummy\>encNonce<around*|(|l<around*|[|nonce|]>|)>\<cdummy\><next-line>BE<rsub|256><around*|(|SHA256<around*|(|l<around*|[|pubScript|]>|)>|)>>>>>
  </eqnarray*>

  and where <math|nullDatum> is defined in the next section.

  <subsection|Null Data>

  An output's scriptPubKey is call a <verbatim|TX_NULL_DATA> script if it
  consists of an <verbatim|OP_RETURN> opcode
  (<math|<around*|\<lceil\>|<math-tt|6a><rsub|<2><rsup|8>>|\<rceil\>>>)
  followed by ``<verbatim|PushOnly>'', operations, which are operations whose
  opcode is <verbatim|OP_16> (96) or less (including <verbatim|OP_RESERVED>
  (80)).

  In Elements, pegouts have an instance of a <verbatim|TX_NULL_DATA>
  scriptPubKey. For that reason we offer primitives for detecting and parsing
  <verbatim|TX_NULL_DATA> scriptPubKeys. Below we define the function

  <\equation*>
    nullData\<of\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>\<rightarrow\><maybe><around*|(|<around*|(|<2><rsup|2>\<times\><2><rsup|256>+<around*|(|<2>+<2><rsup|4>|)>|)><rsup|*\<ast\>>|)>
  </equation*>

  which,

  <\enumerate-numeric>
    <item>decides if a script is ``<verbatim|PushOnly>'', and

    <item>if it is push only, returns a list of parsed opcodes in which the
    pushed data is hashed.
  </enumerate-numeric>

  We also define

  <\equation*>
    nullData\<of\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>\<times\>\<bbb-N\>\<rightarrow\><maybe><around*|(|<maybe><around*|(|<2><rsup|2>\<times\><2><rsup|256>+<around*|(|<2>+<2><rsup|4>|)>|)><rsup|>|)>
  </equation*>

  which decides if a script is <verbatim|TX_NULL_DATA> and returns the parsed
  element at the given index for the parsed data, if length of the parsed
  script is long enough. This is used to define the semantics of
  <samp|outputNullDatum> above.

  <\eqnarray*>
    <tformat|<table|<row|<cell|nullData<around*|(|\<epsilon\><rsub|<2><rsup|8>>|)>>|<cell|\<assign\>>|<cell|\<eta\><rsup|<maybe>><around*|(|\<epsilon\><rsub|<2><rsup|2>\<times\><2><rsup|256>+<around*|(|<2>+<2><rsup|4>|)>>|)>>>|<row|<cell|nullData<around*|(|n\<blacktriangleleft\>d\<cdummy\>l|)>>|<cell|\<assign\>>|<cell|\<mu\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>r.<injl|<around*|\<langle\>|<around*|\<lfloor\>|0|\<rfloor\>><rsub|2>,SHA256<around*|(|d|)>|\<rangle\>>>\<blacktriangleleft\>r|)><around*|(|nullData<around*|(|l|)>|)>|)><next-line><htab|5mm>when
    <around*|\||d|\|>=<around*|\<lceil\>|n|\<rceil\>><rsub|8>\<less\>76>>|<row|<cell|nullData<around*|(|n\<blacktriangleleft\>l|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><htab|5mm>when
    <around*|\||l|\|>\<less\><around*|\<lceil\>|n|\<rceil\>><rsub|8>\<less\>76>>|<row|<cell|nullData<around*|(|<math|<around*|\<lfloor\>|76|\<rfloor\>><rsub|8>>\<blacktriangleleft\>n\<blacktriangleleft\>d\<cdummy\>l|)>>|<cell|\<assign\>>|<cell|\<mu\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>r.<injl|<around*|\<langle\>|<around*|\<lfloor\>|1|\<rfloor\>><rsub|2>,SHA256<around*|(|d|)>|\<rangle\>>>\<blacktriangleleft\>r|)><around*|(|nullData<around*|(|l|)>|)>|)><next-line><htab|5mm>when
    <around*|\||d|\|>=<around*|\<lceil\>|n|\<rceil\>><rsub|8>>>|<row|<cell|nullData<around*|(|<around*|\<lfloor\>|76|\<rfloor\>><rsub|8>\<blacktriangleleft\>n\<blacktriangleleft\>l|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><htab|5mm>when
    <around*|\||l|\|>\<less\><around*|\<lceil\>|n|\<rceil\>><rsub|8>>>|<row|<cell|nullData<around*|(|<around*|\<lfloor\>|76|\<rfloor\>><rsub|8>\<blacktriangleleft\>\<varepsilon\>|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>>>>|<row|<cell|nullData<around*|(|<around*|\<lfloor\>|77|\<rfloor\>><rsub|8>\<blacktriangleleft\>n<rsub|1>\<blacktriangleleft\>n<rsub|0>\<blacktriangleleft\>d\<cdummy\>l|)>>|<cell|\<assign\>>|<cell|\<mu\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>r.<injl|<around*|\<langle\>|<around*|\<lfloor\>|2|\<rfloor\>><rsub|2>,SHA256<around*|(|d|)>|\<rangle\>>>\<blacktriangleleft\>r|)><around*|(|nullData<around*|(|l|)>|)>|)><next-line><htab|5mm>when
    <around*|\||d|\|>=<around*|\<lceil\>|<around*|\<langle\>|n<rsub|0>,n<rsub|1>|\<rangle\>>|\<rceil\>><rsub|16>>>|<row|<cell|nullData<math|<around*|(|<around*|\<lfloor\>|77|\<rfloor\>><rsub|8>\<blacktriangleleft\>n<rsub|1>\<blacktriangleleft\>n<rsub|0>\<blacktriangleleft\>l|)>>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><htab|5mm>when
    <around*|\||l|\|>\<less\><around*|\<lceil\>|<around*|\<langle\>|n<rsub|0>,n<rsub|1>|\<rangle\>>|\<rceil\>><rsub|16>>>|<row|<cell|nullData<around*|(|<math|<around*|\<lfloor\>|77|\<rfloor\>><rsub|8>>\<blacktriangleleft\>l|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><htab|5mm>when
    <around*|\||l|\|>\<less\>2>>|<row|<cell|nullData<around*|(|<around*|\<lfloor\>|78|\<rfloor\>><rsub|8>\<blacktriangleleft\>n<rsub|3>\<blacktriangleleft\>n<rsub|2>\<blacktriangleleft\>n<rsub|1>\<blacktriangleleft\>n<rsub|0>\<blacktriangleleft\>d\<cdummy\>l|)>>|<cell|\<assign\>>|<cell|\<mu\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>r.<injl|<around*|\<langle\>|<around*|\<lfloor\>|3|\<rfloor\>><rsub|2>,SHA256<around*|(|d|)>|\<rangle\>>>\<blacktriangleleft\>r|)><around*|(|nullData<around*|(|l|)>|)>|)><next-line><htab|5mm>when
    <around*|\||d|\|>=<around*|\<lceil\>|<around*|\<langle\>|<around*|\<langle\>|n<rsub|0>,n<rsub|1>|\<rangle\>>,<around*|\<langle\>|n<rsub|2>,n<rsub|3>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|32>>>|<row|<cell|nullData<around*|(|<around*|\<lfloor\>|78|\<rfloor\>><rsub|8>\<blacktriangleleft\>n<rsub|3>\<blacktriangleleft\>n<rsub|2>\<blacktriangleleft\>n<rsub|1>\<blacktriangleleft\>n<rsub|0>\<blacktriangleleft\>l|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><htab|5mm>when
    <around*|\||l|\|>\<less\><around*|\<lceil\>|<around*|\<langle\>|<around*|\<langle\>|n<rsub|0>,n<rsub|1>|\<rangle\>>,<around*|\<langle\>|n<rsub|2>,n<rsub|3>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|32>>>|<row|<cell|nullData<around*|(|<around*|\<lfloor\>|78|\<rfloor\>><rsub|8>\<blacktriangleleft\>l|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><htab|5mm>when
    <around*|\||l|\|>\<less\>4>>|<row|<cell|nullData<around*|(|<around*|\<lfloor\>|79|\<rfloor\>><rsub|8>\<blacktriangleleft\>l|)>>|<cell|\<assign\>>|<cell|\<mu\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>r.<injr|<around*|(|<injl|<around*|(|<math-tt|0><rsub|<2>>|)>>|)>>\<blacktriangleleft\>r|)><around*|(|nullData<around*|(|l|)>|)>|)>>>|<row|<cell|nullData<around*|(|<around*|\<lfloor\>|80|\<rfloor\>><rsub|8>\<blacktriangleleft\>l|)>>|<cell|\<assign\>>|<cell|\<mu\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>r.<injr|<around*|(|<injl|<around*|(|<math-tt|1><rsub|<2>>|)>>|)>>\<blacktriangleleft\>r|)><around*|(|nullData<around*|(|l|)>|)>|)>>>|<row|<cell|nullData<around*|(|x\<blacktriangleleft\>l|)>>|<cell|\<assign\>>|<cell|\<mu\><rsup|<maybe>><around*|(|<maybe><around*|(|\<lambda\>r.<injr|<around*|(|<injr|<around*|\<lfloor\>|<around*|\<lceil\>|x|\<rceil\>><rsub|8>-81|\<rfloor\>><rsub|4>>|)>>\<blacktriangleleft\>r|)><around*|(|nullData<around*|(|l|)>|)>|)><next-line><htab|5mm>when
    81\<leq\><around*|\<lceil\>|x|\<rceil\>><rsub|8>\<less\>97>>|<row|<cell|nullData<around*|(|x\<blacktriangleleft\>l|)>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><htab|5mm>when
    97\<leq\><around*|\<lceil\>|x|\<rceil\>><rsub|8>>>|<row|<cell|nullDatum<around*|\<langle\>|<math-tt|6a><rsub|<2><rsup|8>>\<blacktriangleleft\>s,j|\<rangle\>>>|<cell|\<assign\>>|<cell|<maybe><around*|(|\<lambda\>l.l<around*|[|j|]>|)><around*|(|nullData<around*|(|s|)>|)>>>|<row|<cell|nullDatum<around*|\<langle\>|x\<blacktriangleleft\>s,j|\<rangle\>>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>><htab|5mm><text|when
    <math|x\<neq\>><math|<math-tt|6a><rsub|<2><rsup|8>>>>>>|<row|<cell|nullDatum<around*|\<langle\>|\<epsilon\>,j|\<rangle\>>>|<cell|\<assign\>>|<cell|\<emptyset\><rsup|<maybe>>>>>>
  </eqnarray*>

  <subsection|Merkle Roots>

  We extend the definition of the commitment Merkle root to support the new
  expressions by hashing new unique byte strings.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<cmr|<math-ss|version>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[76657273696f6e]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|lockTime>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[6c6f636b54696d65]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|inputsHash>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[696e7075747348617368]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|outputsHash>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[6f75747075747348617368]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|numInputs>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[6e756d496e70757473]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|inputIsPegin>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[696e7075744973506567696e]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|inputPrevOutpoint>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[696e707574507265764f7574706f696e74]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|inputAsset>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[696e7075744173736574]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|inputAmount>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[696e707574416d6f756e74]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|inputScriptHash>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|ELprefix\<cdummy\><math-tt|[696e70757453637269707448617368]>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|inputSequence>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[696e70757453657175656e6365]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|inputIssuanceBlinding>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[696e70757449737375616e6365426c696e64696e67]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|inputIssuanceContract>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[696e70757449737375616e6365436f6e7472616374]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|inputIssuanceEntropy>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[696e70757449737375616e6365456e74726f7079]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|inputIssuanceAssetAmt>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[696e70757449737375616e63654173736574416d74]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|inputIssuanceTokenAmt>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[696e70757449737375616e6365546f6b656e416d74]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|currentIndex>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[63757272656e74496e646578]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|currentIsPegin>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[63757272656e744973506567696e]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|currentPrevOutpoint>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[63757272656e74507265764f7574706f696e74]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|currentAsset>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[63757272656e744173736574]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|currentAmount>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[63757272656e74416d6f756e74]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|currentScriptHash>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[63757272656e7453637269707448617368]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|currentSequence>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[63757272656e7453657175656e6365]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|currentIssuanceBlinding>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[63757272656e7449737375616e6365426c696e64696e67]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|currentIssuanceContract>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[63757272656e7449737375616e6365436f6e7472616374]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|currentIssuanceEntropy>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[63757272656e7449737375616e6365456e74726f7079]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|currentIssuanceAssetAmt>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[63757272656e7449737375616e63654173736574416d74]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|currentIssuanceTokenAmt>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[63757272656e7449737375616e6365546f6b656e416d74]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|numOutput>s>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[6e756d784f757470757473]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|outputAsset>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[6f75747075744173736574]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|outputAmount>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[6f7574707574416d6f756e74]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|outputNonce>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[6f75747075744e6f6e6365]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|outputScriptHash>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[6f757470757453637269707448617368]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|outputNullDatum>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[6f75747075744e756c6c446174756d]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|fee>>>|<cell|\<assign\>>|<cell|SHA256<rsup|<math|ELprefix\<cdummy\><math-tt|[666565]>>><rsub|IV>>>|<row|<cell|<cmr|<math-ss|<math|scriptCMR>>>>|<cell|\<assign\>>|<cell|SHA256<rsup|ELprefix\<cdummy\><math-tt|[736372697074434d52]>><rsub|IV>>>>>
  </eqnarray*>

  \;

  where

  <\equation*>
    ELprefix\<assign\><math-tt|[<SimplicityPrefix>1f5072696d69746976651f456c656d6e74731f]>
  </equation*>

  <subsection|Serialization>

  Below we give codes for Elements primitive names. The prefix codes for
  primitive names all begin with <math|<verbatim|[10]><rsub|<2>>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<rep|<text|<samp|`version'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10000000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`lockTime'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10000001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputIsPegin'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputPrevOutpoint'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000010|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputAsset'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000011|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputAmount'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10001000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputScriptHash'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10001001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputSequence'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000101|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputIssuanceBlinding'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000110|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputIssuanceContract'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000111|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputIssuanceEntropy'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10010000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputIssuanceAssetAmt'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10010001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputIssuanceTokenAmt'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1001001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputAsset'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1001010|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputAmount'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1001011|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputNonce'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10011000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputScriptHash'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10011001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputNullDatum'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1001101|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`scriptCMR'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1001110|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentIsPegin'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentPrevOutpoint'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentAsset'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010010|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentAmount'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010011|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentScriptHash'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010100|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentSequence'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010101|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentIssuanceBlinding'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010110|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentIssuanceContract'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010111|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentIssuanceEntropy'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1011000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentIssuanceAssetAmt'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1011001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentIssuanceTokenAmt'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1011010|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputsHash'>>|>>|<cell|=>|<cell|<rsub|><verbatim|<around*|[|1011011|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputsHash'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1011100|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`numInputs'>>|>>|<cell|=>|<verbatim|<around*|[|1011101|]>><rsub|<2>>>|<row|<cell|<rep|<text|<samp|`numOutputs'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1011110|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`fee'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1011111|]>><rsub|<2>>>>>>
  </eqnarray*>

  <appendix|Catelogue of Jets>

  <assign|paragraph-title|<macro|name|<sectional-normal-bold|<the-paragraph><hspace|0.75em><arg|name>>>><with|color|red|UNDER
  DEVELOPMENT AND SUBJECT TO CHANGE>

  \;

  We develop a recommended set of jets and provide an interm encoding. \ An
  encoding ought to be based on how frequenly jets are used, however we do
  not currently have good estimates of that. \ As an interm measure we
  develop a heirarchical encoding of jets by category.

  The properties for jets listed below may not fully define the jet's
  semantics. All jets will be formally specified by a Simplicity program that
  implements their complete semantics. \ Those formal specificaitons will be
  found in the Coq library. Implementations MUST implement the COMPLETE
  specifications as defined in the Coq library.

  <section|<verbatim|110...: >Core Jets>

  \;

  The following jets are specified in core Simplicity or Simplicity with
  assertions, and therefore are applicable to any Simplicity application.

  <subsection|<verbatim|1100...: >Jets for multi-bit logic>

  It is recomended that jets be supported for multi-bit words up to
  <math|<2><rsup|256>> in size.

  <with|color|red|TODO: define <math|bit<rsub|n,m> :
  <2><rsup|n>\<rightarrow\><2>>>

  <subsubsection|<samp|low>>

  \;

  <math|<rep|<text|<samp|'low'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|low>><rsub|2<rsup|n>>\<of\><1>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|<around*|\<llbracket\>|<text|<samp|low>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>||\<rangle\>>|)>|\<rceil\>><rsub|1>=0>

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|low>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>||\<rangle\>>|\<rceil\>><rsub|2<rsup|n>>=0>

  \;

  Aliases:

  <math|<math|<text|<samp|zero>>><rsub|2<rsup|n>> \<assign\>
  <text|<samp|low>><rsub|2<rsup|n>>\<of\><1>\<vdash\><2><rsup|2<rsup|n>>>

  <subsubsection|<samp|high>>

  \;

  <math|<rep|<text|<samp|'high'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|high>><rsub|2<rsup|n>>\<of\><1>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|<around*|\<llbracket\>|<text|<samp|high>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>||\<rangle\>>|)>|\<rceil\>><rsub|1>=1>

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|high>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>||\<rangle\>>|\<rceil\>><rsub|2<rsup|n>>=2<rsup|n>-1>

  \;

  Aliases:

  <math|<math|<text|<samp|one>><rsub|1>> \<assign\>
  <text|<samp|high>><rsub|1>\<of\><1>\<vdash\><2>>

  <subsubsection|<samp|complement>>

  \;

  <math|<rep|<text|<samp|'complement'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|complement>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>> for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|<around*|\<llbracket\>|<text|<samp|complement>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>|)>|\<rceil\>><rsub|1>=1-<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|x|)>|\<rceil\>><rsub|1>>

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|complement>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>|\<rceil\>><rsub|2<rsup|n>>=2<rsup|n>-1-<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>>

  <subsubsection|<samp|and>>

  \;

  <\math>
    <rep|<text|<samp|'and'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>
  </math>

  <math|<text|<samp|and>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|<around*|\<llbracket\>|<text|<samp|and>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|\<rceil\>><rsub|1>=\<chi\><around*|(|<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|x|)>|\<rceil\>><rsub|1>=1\<wedge\><around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|y|)>|\<rceil\>><rsub|1>=1|)>>

  <subsubsection|<samp|or>>

  \;

  <\math>
    <rep|<text|<samp|'or'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>
  </math>

  <math|<text|<samp|or>><rsub|2<rsup|n>> :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|<around*|\<llbracket\>|<text|<samp|or>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|\<rceil\>><rsub|1>=\<chi\><around*|(|<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|x|)>|\<rceil\>><rsub|1>=1\<vee\><around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|y|)>|\<rceil\>><rsub|1>=1|)>>

  <subsubsection|<samp|xor>>

  \;

  <\math>
    <rep|<text|<samp|'xor'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>
  </math>

  <math|<text|<samp|xor>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|<around*|\<llbracket\>|<text|<samp|xor>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|\<rceil\>><rsub|1>\<equiv\><around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|x|)>|\<rceil\>><rsub|1>+<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|y|)>|\<rceil\>><rsub|1><around*|(|mod
  2|)>>

  <subsubsection|<samp|maj>>

  \;

  <\math>
    <rep|<text|<samp|'maj'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>
  </math>

  <math|<text|<samp|maj>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><around*|(|<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>|)>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|<around*|\<llbracket\>|<text|<samp|maj>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,<around*|\<langle\>|y,z|\<rangle\>>|\<rangle\>>|)>|\<rceil\>><rsub|1>=\<chi\><around*|(|2\<leq\><around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|x|)>|\<rceil\>><rsub|1>+<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|y|)>|\<rceil\>><rsub|1>+<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|z|)>|\<rceil\>><rsub|1>|)>>

  <subsubsection|<samp|xor3>>

  \;

  <\math>
    <rep|<text|<samp|'xor3'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>
  </math>

  <math|<text|<samp|xor3>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><around*|(|<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>|)>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|<around*|\<llbracket\>|<text|<samp|xor3>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,<around*|\<langle\>|y,z|\<rangle\>>|\<rangle\>>|)>|\<rceil\>><rsub|1>\<equiv\><around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|x|)>|\<rceil\>><rsub|1>+<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|y|)>|\<rceil\>><rsub|1>+<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|z|)>|\<rceil\>><rsub|1><around*|(|mod
  2|)>>

  <subsubsection|<samp|ch>>

  \;

  <\math>
    <rep|<text|<samp|'ch'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>
  </math>

  <math|<text|<samp|ch>><rsub|2<rsup|n>> :<2><rsup|2<rsup|n>>\<times\><around*|(|<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>|)>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|<around*|\<llbracket\>|<text|<samp|ch>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,<around*|\<langle\>|y,z|\<rangle\>>|\<rangle\>>|)>|\<rceil\>><rsub|1>=<around*|(|1-<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|x|)>|\<rceil\>><rsub|1>|)>\<cdot\><around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|y|)>|\<rceil\>><rsub|1>+<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|x|)>|\<rceil\>><rsub|1>\<cdot\><around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|z|)>|\<rceil\>><rsub|1>>

  <subsubsection|<samp|some>>

  (CAUTION: Not defined when <math|n=0>.)

  <math|<rep|<text|<samp|'some'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|some>><rsub|2<rsup|n>> :<2><rsup|2<rsup|n>>\<vdash\><2>>
  for <math|1\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|some>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>|\<rceil\>><rsub|1>=\<chi\><around*|(|<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>\<neq\>0|)>>

  \;

  Aliases:

  <math|<math|<text|<samp|some>><rsub|1>> \<assign\> <text|<samp|iden>>
  \<of\> <2>\<vdash\><2>>

  <subsubsection|<samp|all>>

  (CAUTION: Not defined when <math|n=0>.)

  <math|<rep|<text|<samp|'all'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|all>><rsub|2<rsup|n>> :<2><rsup|2<rsup|n>>\<vdash\><2>>
  for <math|1\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|all>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>|\<rceil\>><rsub|1>=\<chi\><around*|(|<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>=2<rsup|n>-1|)>>

  \;

  Aliases:

  <math|<math|<text|<samp|all>><rsub|1>> \<assign\> <text|<samp|iden>> \<of\>
  <2>\<vdash\><2>>

  <subsubsection|<samp|eq>>

  \;

  <\math>
    <rep|<text|<samp|'eq'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>
  </math>

  <math|<text|<samp|eq>><rsub|2<rsup|n>> :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<llbracket\>|<text|<samp|eq>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>=\<chi\><around*|(|x=y|)>>

  <subsubsection|<samp|full-left-shift>>

  \;

  <\math>
    <rep|<text|<samp|'full-left-shift'>><rsub|2<rsup|n>,2<rsup|m>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|m+1|>\<cdummy\><rep|n-m|>
  </math>

  <math|<text|<samp|full-left-shift>><rsub|2<rsup|n>,2<rsup|m>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|m>>\<vdash\><2><rsup|2<rsup|m>>\<times\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>m\<less\>n>

  \;

  Properties:

  <math|bit<rsub|2<rsup|m>,i><around*|(|\<pi\><rsub|1><around*|(|<around*|\<llbracket\>|<text|<samp|full-left-shift>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|)>=bit<rsub|2<rsup|n>,i><around*|(|x|)>>
  for <math|0\<leq\>i\<less\>2<rsup|m>>

  <math|bit<rsub|2<rsup|n>,i><around*|(|\<pi\><rsub|2><around*|(|<around*|\<llbracket\>|<text|<samp|full-left-shift>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|)>=bit<rsub|2<rsup|n>,2<rsup|m>+i><around*|(|x|)>>
  for <math|0\<leq\>i\<less\>2<rsup|n>-2<rsup|m>>

  <math|bit<rsub|2<rsup|n>,2<rsup|n>-2<rsup|m>+i><around*|(|\<pi\><rsub|2><around*|(|<around*|\<llbracket\>|<text|<samp|full-left-shift>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|)>=bit<rsub|2<rsup|m>,i><around*|(|y|)>>
  for <math|0\<leq\>i\<less\>2<rsup|m>>

  \;

  Aliases:

  <math|<text|<samp|full-left-shift>><rsub|2<rsup|n>,2<rsup|n>> \<assign\>
  <text|<samp|iden>> :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>>

  <math|<text|<samp|full-left-shift>><rsub|2<rsup|n>,2<rsup|m>>
  \<assign\><text|<samp|full-right-shift>><rsub|2<rsup|m>,2<rsup|n>>:<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|m>>\<vdash\><2><rsup|2<rsup|m>>\<times\><2><rsup|2<rsup|n>>>
  when <math|0\<leq\>n\<less\>m>

  <math|<text|<samp|full-right-shift>><rsub|2<rsup|n>,2<rsup|m>>
  \<assign\><text|<samp|full-left-shift>><rsub|2<rsup|m>,2<rsup|n>>
  :<2><rsup|2<rsup|m>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|m>>>
  when <math|0\<leq\>n\<less\>m>

  <subsubsection|<samp|full-right-shift>>

  \;

  <\math>
    <rep|<text|<samp|'full-right-shift'>><rsub|2<rsup|n>,2<rsup|m>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|m+1|>\<cdummy\><rep|n-m|>
  </math>

  <math|<text|<samp|full-right-shift>><rsub|2<rsup|n>,2<rsup|m>>
  :<2><rsup|2<rsup|m>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|m>>>
  for <math|0\<leq\>m\<less\>n>

  \;

  Properties:

  <math|bit<rsub|2<rsup|n>,i><around*|(|\<pi\><rsub|1><around*|(|<around*|\<llbracket\>|<text|<samp|full-right-shift>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|)>=bit<rsub|k><around*|(|x|)>>
  for <math|0\<leq\>i\<less\>2<rsup|m>>

  <math|bit<rsub|2<rsup|n>,2<rsup|m>+i><around*|(|\<pi\><rsub|1><around*|(|<around*|\<llbracket\>|<text|<samp|full-right-shift>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|)>=bit<rsub|2<rsup|n>,i><around*|(|y|)>>
  for <math|0\<leq\>i\<less\>2<rsup|n>-2<rsup|m>>

  <math|bit<rsub|2<rsup|m>,i><around*|(|\<pi\><rsub|2><around*|(|<around*|\<llbracket\>|<text|<samp|full-right-shift>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|)>=bit<rsub|2<rsup|n>,2<rsup|n>-2<rsup|m>+i><around*|(|y|)>>
  for <math|0\<leq\>i\<less\>2<rsup|m>>

  \;

  Aliases:

  <math|<text|<samp|full-right-shift>><rsub|2<rsup|n>,2<rsup|n>> \<assign\>
  <text|<samp|iden>> :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>>

  <math|<text|<samp|full-right-shift>><rsub|2<rsup|n>,2<rsup|m>>
  \<assign\><text|<samp|full-left-shift>><rsub|2<rsup|m>,2<rsup|n>>
  :<2><rsup|2<rsup|m>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|m>>>
  when <math|0\<leq\>n\<less\>m>

  <math|<text|<samp|full-left-shift>><rsub|2<rsup|n>,2<rsup|m>>
  \<assign\><text|<samp|full-right-shift>><rsub|2<rsup|m>,2<rsup|n>>:<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|m>>\<vdash\><2><rsup|2<rsup|m>>\<times\><2><rsup|2<rsup|n>>>
  when <math|0\<leq\>n\<less\>m>

  <subsubsection|<samp|leftmost>>

  \;

  <\math>
    <rep|<text|<samp|'leftmost'>><rsub|2<rsup|n>,2<rsup|m>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdot\><rep|m+1|>\<cdummy\><rep|n-m|>
  </math>

  <math|<text|<samp|leftmost>><rsub|2<rsup|n>,2<rsup|m>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|m>>> for
  <math|0\<leq\>m\<less\>n>

  \;

  Properties:

  <math|bit<rsub|2<rsup|m>,i><around*|(|<around*|\<llbracket\>|<text|<samp|leftmost>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>=bit<rsub|2<rsup|n>,i><around*|(|x|)>>

  \;

  Aliases:

  <math|<text|<samp|leftmost>><rsub|2<rsup|n>,2<rsup|n>> \<assign\>
  <text|<samp|iden>> :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>

  <subsubsection|<samp|rightmost>>

  \;

  <\math>
    <rep|<text|<samp|'rightmost'>><rsub|2<rsup|n>,2<rsup|m>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdot\><rep|m+1|>\<cdummy\><rep|n-m|>
  </math>

  <math|<text|<samp|rightmost>><rsub|2<rsup|n>,2<rsup|m>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|m>>> for
  <math|0\<leq\>m\<less\>n>

  \;

  Properties:

  <math|bit<rsub|2<rsup|m>,i><around*|(|<around*|\<llbracket\>|<text|<samp|rightmost>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>=bit<rsub|2<rsup|n>,2<rsup|n>-2<rsup|m>+i><around*|(|x|)>>

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|rightmost>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|\<rceil\>><rsub|2<rsup|m>>=<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>
  <around*|(|mod 2<rsup|m>|)>>

  \;

  Aliases:

  <math|<text|<samp|rightmost>><rsub|2<rsup|n>,2<rsup|n>> \<assign\>
  <text|<samp|iden>> :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>

  <subsubsection|<samp|left-pad-low>>

  (Note: derived from <samp|full-left-shift>.)

  <\math>
    <rep|<text|<samp|'left-pad-low'>><rsub|2<rsup|n>,2<rsup|m>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>\<cdummy\><rep|m-n|>
  </math>

  <math|<text|<samp|left-pad-low>><rsub|2<rsup|n>,2<rsup|m>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|m>>> for
  <math|0\<leq\>n\<less\>m>

  \;

  Properties:

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|m>,i><around*|(|<around*|\<llbracket\>|<text|<samp|left-pad-low>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>|\<rceil\>><rsub|1>=0>
  when <math|i\<less\>2<rsup|m>-2<rsup|n>>

  <math|bit<rsub|2<rsup|m>,2<rsup|m>-2<rsup|n>+i><around*|(|<around*|\<llbracket\>|<text|<samp|left-pad-low>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>=bit<rsub|2<rsup|n>,i><around*|(|x|)>>
  when <math|i\<less\>2<rsup|n>>

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|left-pad-low>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|\<rceil\>><rsub|2<rsup|m>>=<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>>

  <subsubsection|<samp|left-pad-high>>

  (Note: derived from <samp|full-left-shift>.)

  <\math>
    <rep|<text|<samp|'left-pad-high'>><rsub|2<rsup|n>,2<rsup|m>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>\<cdummy\><rep|m-n|>
  </math>

  <math|<text|<samp|left-pad-high>><rsub|2<rsup|n>,2<rsup|m>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|m>>> for
  <math|0\<leq\>n\<less\>m>

  \;

  Properties:

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|m>,i><around*|(|<around*|\<llbracket\>|<text|<samp|left-pad-high>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>|\<rceil\>><rsub|1>=1>
  when <math|i\<less\>2<rsup|m>-2<rsup|n>>

  <math|bit<rsub|2<rsup|m>,2<rsup|m>-2<rsup|n>+i><around*|(|<around*|\<llbracket\>|<text|<samp|left-pad-high>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>=bit<rsub|2<rsup|n>,i><around*|(|x|)>>
  when <math|i\<less\>2<rsup|n>>

  <subsubsection|<samp|left-extend>>

  (Note: derived from <samp|leftmost>, <samp|left-pad-low> and
  <samp|left-pad-high>.)

  <\math>
    <rep|<text|<samp|'left-extend'>><rsub|2<rsup|n>,2<rsup|m>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>\<cdummy\><rep|m-n|>
  </math>

  <math|<text|<samp|left-extend>><rsub|2<rsup|n>,2<rsup|m>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|m>>> for
  <math|0\<leq\>n\<less\>m>

  \;

  Properties:

  <math|bit<rsub|2<rsup|m>,i><around*|(|<around*|\<llbracket\>|<text|<samp|left-extend>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>=bit<rsub|2<rsup|n>,0><around*|(|x|)>>
  when <math|i\<less\>2<rsup|n>-2<rsup|>>

  <math|bit<rsub|2<rsup|m>,2<rsup|m>-2<rsup|n>+i><around*|(|<around*|\<llbracket\>|<text|<samp|left-extend>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>=bit<rsub|2<rsup|n>,i><around*|(|x|)>>
  when <math|i\<less\>2<rsup|n>>

  \;

  Aliases:

  <math|<text|<samp|right-extend>><rsub|1,2<rsup|m>>\<assign\><text|<samp|left-extend>><rsub|1,2<rsup|m>>
  :<2><rsup|>\<vdash\><2><rsup|2<rsup|m>>> for <math|0\<leq\>n\<less\>m>

  <subsubsection|<samp|right-pad-low>>

  (Note: derived from <samp|full-right-shift>.)

  <\math>
    <rep|<text|<samp|'right-pad-low'>><rsub|2<rsup|n>,2<rsup|m>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>\<cdummy\><rep|m-n|>
  </math>

  <math|<text|<samp|right-pad-low>><rsub|2<rsup|n>,2<rsup|m>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|m>>> for
  <math|0\<leq\>n\<less\>m>

  \;

  Properties:

  <math|bit<rsub|2<rsup|m>,i><around*|(|<around*|\<llbracket\>|<text|<samp|right-pad-low>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>=bit<rsub|2<rsup|n>,i><around*|(|x|)>>
  when <math|i\<less\>2<rsup|n>>

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|m>,i><around*|(|<around*|\<llbracket\>|<text|<samp|right-pad-low>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>|\<rceil\>><rsub|1>=0>
  when <math|2<rsup|n>\<leq\>i\<less\>2<rsup|m>>

  <subsubsection|<samp|right-pad-high>>

  (Note: derived from <samp|full-right-shift>.)

  <\math>
    <rep|<text|<samp|'right-pad-high'>><rsub|2<rsup|n>,2<rsup|m>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>\<cdummy\><rep|m-n|>
  </math>

  <math|<text|<samp|right-pad-high>><rsub|2<rsup|n>,2<rsup|m>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|m>>> for
  <math|0\<leq\>n\<less\>m>

  \;

  Properties:

  <math|bit<rsub|2<rsup|m>,i><around*|(|<around*|\<llbracket\>|<text|<samp|right-pad-high>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>=bit<rsub|2<rsup|n>,i><around*|(|x|)>>
  when <math|i\<less\>2<rsup|n>>

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|m>,i><around*|(|<around*|\<llbracket\>|<text|<samp|right-pad-high>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>|\<rceil\>><rsub|1>=1>
  when <math|2<rsup|n>\<leq\>i\<less\>2<rsup|m>>

  <subsubsection|<samp|right-extend>>

  (Note: derived from <samp|rightmost>, <samp|right-pad-low>, and
  <samp|right-pad-high>.)

  (CAUTION: Not defined when <math|n=0>.)

  <\math>
    <rep|<text|<samp|'right-extend'>><rsub|2<rsup|n>,2<rsup|m>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>\<cdummy\><rep|m-n|>
  </math>

  <math|<text|<samp|right-extend>><rsub|2<rsup|n>,2<rsup|m>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|m>>> for
  <math|1\<leq\>n\<less\>m>\ 

  \;

  Properties:

  <math|bit<rsub|2<rsup|m>,i><around*|(|<around*|\<llbracket\>|<text|<samp|right-extend>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>=bit<rsub|2<rsup|n>,i><around*|(|x|)>>
  when <math|i\<less\>2<rsup|n>>

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|m>,i><around*|(|<around*|\<llbracket\>|<text|<samp|right-extend>><rsub|2<rsup|n>,2<rsup|m>>|\<rrbracket\>><around*|(|x|)>|)>|\<rceil\>><rsub|1>=bit<rsub|2<rsup|n>,2<rsup|n>-1><around*|(|x|)>>
  when <math|2<rsup|n>\<leq\>i\<less\>2<rsup|m>>

  \;

  Aliases:

  <math|<text|<samp|right-extend>><rsub|1,2<rsup|m>>\<assign\><text|<samp|left-extend>><rsub|1,2<rsup|m>>
  :<2><rsup|>\<vdash\><2><rsup|2<rsup|m>>> for <math|0\<leq\>n\<less\>m>

  <subsubsection|<samp|right-shift-with>>

  Right shift by a signed amount. Negative values are a left shift. \ Bits
  are filled with the provided value.

  <\math>
    <rep|<text|<samp|'right-shift-with'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>
  </math>

  <math|<text|<samp|right-shift-with>><rsub|2<rsup|n>>
  :<2>\<times\><around*|(|<2><rsup|2<rsup|<around*|\<lceil\>|lg<around*|(|n+1|)>|\<rceil\>>>>\<times\><2><rsup|2<rsup|n>>|)>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  <subsubsection|<samp|right-shift>>

  Right shift by a signed amount. Negative values are a left shift.

  <\math>
    <rep|<text|<samp|'right-shift'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>
  </math>

  <math|<text|<samp|right-shift>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|<around*|\<lceil\>|lg<around*|(|n+1|)>|\<rceil\>>>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  <subsubsection|<samp|right-rotate>>

  Right rotate by an amount.

  <\math>
    <rep|<text|<samp|'right-rotate'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>
  </math>

  <math|<text|<samp|right-rotate>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|<around*|\<lceil\>|lg<around*|(|n|)>|\<rceil\>>>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|1\<leq\>n>

  \;

  Aliases:

  <math|<math|<text|<samp|right-rotate>><rsub|1>> \<assign\>
  <text|<samp|drop>> \<of\> <1>\<times\><2>\<vdash\><2>>

  <subsubsection|<samp|transpose>>

  (CAUTION: Not defined when <math|n=0> or <math|m=0>.)

  (Note: Support only recommened up to <math|2<rsup|n>\<cdot\>2<rsup|m>\<leq\>256>.)

  <\math>
    <rep|<text|<samp|'transpose'>><rsub|2<rsup|n>,2<rsup|m>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>\<cdummy\><rep|m|>
  </math>

  <math|<text|<samp|transpose>><rsub|2<rsup|n>,2<rsup|m>>
  :<2><rsup|2<rsup|n>\<cdummy\>2<rsup|m>>\<vdash\><2><rsup|2<rsup|m>\<cdummy\>2<rsup|n>>>
  for <math|1\<leq\>n> and <math|1\<leq\>m>

  \;

  Aliases:

  <math|<text|<samp|transpose>><rsub|1,2<rsup|n>> \<assign\>
  <text|<samp|iden>> :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>

  <math|<text|<samp|transpose>><rsub|2<rsup|n>,1> \<assign\>
  <text|<samp|iden>> :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>

  <subsubsection|<samp|find-first-high>>

  (CAUTION: Not defined when <math|n=0>.)

  <\math>
    <rep|<text|<samp|'find-first-high'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>
  </math>

  <math|<text|<samp|find-first-high>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|<around*|\<lceil\>|lg<around*|(|n+1|)>|\<rceil\>>>>>
  for <math|1\<leq\>n>

  <subsubsection|<samp|find-last-high>>

  (CAUTION: Not defined when <math|n=0>.)

  <\math>
    <rep|<text|<samp|'find-last-high'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>
  </math>

  <math|<text|<samp|find-last-high>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|<around*|\<lceil\>|lg<around*|(|n+1|)>|\<rceil\>>>>>
  for <math|1\<leq\>n>

  <subsubsection|<samp|bit>>

  (CAUTION: Not defined when <math|n\<leq\>1>.)

  <\math>
    <rep|<text|<samp|'bit'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n-1|>
  </math>

  <math|<text|<samp|bit>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|<around*|\<lceil\>|lg<around*|(|n|)>|\<rceil\>>>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2>>
  for <math|2\<leq\>n>

  \;

  Aliases:

  <math|<math|<text|<samp|bit>><rsub|1>> \<assign\> <text|<samp|drop>> \<of\>
  <1>\<times\><2>\<vdash\><2>>

  <math|<math|<text|<samp|bit>><rsub|2>> \<assign\> <text|<samp|ch>><rsub|1>
  \<of\> <2>\<times\><2><rsup|2>\<vdash\><2>>

  <subsection|<verbatim|110100...: >Jets for arithmetic>

  <subsubsection|<samp|one>>

  (CAUTION: Not defined when <math|n=0>. See Aliases.)

  <math|<rep|<text|<samp|'one'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|one>><rsub|2<rsup|n>>\<of\><1>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|1\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|<around*|\<llbracket\>|<text|<samp|one>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>|)>|\<rceil\>><rsub|1>=0>
  when <math|0\<leq\>i\<less\>2<rsup|n>-1>

  <math|<around*|\<lceil\>|bit<rsub|2<rsup|n>,2<rsup|n>-1><around*|(|<around*|\<llbracket\>|<text|<samp|one>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>|)>|\<rceil\>><rsub|1>=1>

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|one>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>||\<rangle\>>|\<rceil\>><rsub|2<rsup|n>>=1>

  \;

  Aliases:

  <math|<math|<text|<samp|one>><rsub|1>> \<assign\>
  <text|<samp|high>><rsub|1>\<of\><1>\<vdash\><2>>

  <subsubsection|<samp|full-add>>

  (Note: <math|<text|<samp|'full-add'>><rsub|1>> is composed from
  <samp|`maj`> and <samp|`tri-xor`>.)

  <math|<rep|<text|<samp|'full-add'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|full-add>><rsub|2<rsup|n>>
  :<2>\<times\><around*|(|<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>|)>\<vdash\><2>\<times\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|full-add>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|c,<around*|\<langle\>|x,y|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|1,2<rsup|n>>=<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>+<around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>+<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>>

  <subsubsection|<samp|add>>

  \;

  <math|<rep|<text|<samp|'add'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|add>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2>\<times\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|add>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|\<rceil\>><rsub|1,2<rsup|n>>=<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>+<around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>>

  \;

  Aliases:

  <math|<math|<text|<samp|popcount>><rsub|2>> \<assign\>
  <text|<samp|add>><rsub|1> :<2><rsup|2>\<vdash\><2><rsup|2>>

  <subsubsection|<samp|full-increment>>

  (CAUTION: Not defined when <math|n=0>. See Aliases.)

  <math|<rep|<text|<samp|'full-increment'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|full-increment>><rsub|2<rsup|n>>
  :<2>\<times\><2><rsup|2<rsup|n>>\<vdash\><2>\<times\><2><rsup|2<rsup|n>>>
  for <math|1\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|full-increment>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|c,x|\<rangle\>>|\<rceil\>><rsub|1,2<rsup|n>>=<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>+<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>>

  <subsubsection|<samp|increment>>

  \;

  <math|<rep|<text|<samp|'increment'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|increment>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<vdash\><2>\<times\><2><rsup|2<rsup|n>>> for
  <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|increment>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>|\<rceil\>><rsub|1,2<rsup|n>>=<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>+1>

  <subsubsection|<samp|popcount>>

  (CAUTION: Not defined when <math|n\<leq\>1>.)

  <\math>
    <rep|<text|<samp|'popcount'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n-1|>
  </math>

  <math|<text|<samp|popcount>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|<around*|\<lceil\>|lg<around*|(|n+1|)>|\<rceil\>>>>>
  for <math|1\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|popcount>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>|\<rceil\>><rsub|2<rsup|<around*|\<lceil\>|lg<around*|(|n+1|)>|\<rceil\>>>>=<big|sum><rsub|i=0><rsup|2<rsup|n>-1><around*|\<lceil\>|bit<rsub|2<rsup|n>,i><around*|(|x|)>|\<rceil\>><rsub|1>>

  \;

  Aliases:

  <math|<text|<samp|popcount>><rsub|1> \<assign\> <text|<samp|iden>>
  :<2>\<vdash\><2>>

  <math|<math|<text|<samp|popcount>><rsub|2>> \<assign\>
  <text|<samp|add>><rsub|1> :<2><rsup|2>\<vdash\><2><rsup|2>>

  <subsubsection|<samp|full-subtract>>

  (Note: composition of <samp|full-add> with <samp|complement> applied to 1st
  and 3rd arguments).

  <math|<rep|<text|<samp|'full-subtract'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|full-subtract>><rsub|2<rsup|n>>
  :<2>\<times\><around*|(|<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>|)>\<vdash\><2>\<times\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|full-subtract>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|c,<around*|\<langle\>|x,y|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|1,2<rsup|n>>\<equiv\><around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>-<around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>-<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1><around*|(|mod
  2<rsup|2<rsup|n>+1>|)>>

  <subsubsection|<samp|subtract>>

  \;

  <math|<rep|<text|<samp|'subtract'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|subtract>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2>\<times\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|full-subtract>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|\<rceil\>><rsub|1,2<rsup|n>>\<equiv\><around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>-<around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>><around*|(|mod
  2<rsup|2<rsup|n>+1>|)>>

  <subsubsection|<samp|negate>>

  (CAUTION: Not defined when <math|n=0>.)

  <math|<rep|<text|<samp|'negate'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|negate>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>> for <math|1\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|negate>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>|\<rceil\>><rsub|2<rsup|n>>\<equiv\>-<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>
  <around*|(|mod 2<rsup|2<rsup|n>>|)>>

  <subsubsection|<samp|full-decrement>>

  \;

  <math|<rep|<text|<samp|'full-decrement'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|full-decrement>><rsub|2<rsup|n>>
  :<2>\<times\><2><rsup|2<rsup|n>>\<vdash\><2>\<times\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|full-decrement>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|c,x|\<rangle\>>|\<rceil\>><rsub|1,2<rsup|n>>\<equiv\><around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>-<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1><around*|(|mod
  2<rsup|2<rsup|n>+1>|)>>

  <subsubsection|<samp|decrement>>

  \;

  <math|<rep|<text|<samp|'decrement'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|decrement>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<vdash\><2>\<times\><2><rsup|2<rsup|n>>> for
  <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|decrement>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>|\<rceil\>><rsub|1,2<rsup|n>>\<equiv\><around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>-1<around*|(|mod
  2<rsup|2<rsup|n>+1>|)>>

  <subsubsection|<samp|full-multiply>>

  (Note: <math|<text|<samp|'full-multiply'>><rsub|1>> is composed from
  <math|<text|<samp|'full-add'>><rsub|1>> and <samp|`and`>.)

  <math|<rep|<text|<samp|'full-multiply'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|full-multiply>><rsub|2<rsup|n>>
  :<around*|(|<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>|)>\<times\><around*|(|<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>|)>\<vdash\><2><rsup|2<rsup|n+1>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|full-multiplier>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|c<rsub|1>,c<rsub|2>|\<rangle\>>,<around*|\<langle\>|x,y|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2<rsup|n+1>>=<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>\<cdot\><around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>+<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|2<rsup|n>>+<around*|\<lceil\>|c<rsub|2>|\<rceil\>><rsub|2<rsup|n>>>

  <subsubsection|<samp|multiply>>

  \;

  <math|<rep|<text|<samp|'multiply'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|multiply>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n+1>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|multiply>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|\<rceil\>><rsub|2<rsup|n+1>>=<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>\<cdot\><around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>>

  <subsubsection|<verbatim|><samp|is-zero>>

  (CAUTION: Not defined when <math|n=0>. See Aliases.)

  (Note: <samp|complement> of <samp|some>).

  <math|<rep|<text|<samp|'is-zero'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|is-zero>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>|\<rceil\>><rsub|1>=\<chi\><around*|(|<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>=0|)>>

  <subsubsection|<verbatim|><samp|is-one>>

  (CAUTION: Not defined when <math|n=0>. See Aliases.)

  <math|<rep|<text|<samp|'is-one'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|is-one>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>|\<rceil\>><rsub|1>=\<chi\><around*|(|<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>=1|)>>

  <subsubsection|<samp|le> (unsigned)>

  (Note: borrow bit from <samp|subtractor>)

  <math|<rep|<text|<samp|'le'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|le>><rsub|2<rsup|n>> :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|le>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|\<rceil\>><rsub|1>=\<chi\><around*|(|<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>\<leq\><around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>|)>>

  <subsubsection|<samp|lt> (unsigned)>

  \;

  <math|<rep|<text|<samp|'lt'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|lt>><rsub|2<rsup|n>> :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|lt>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|\<rceil\>><rsub|1>=\<chi\><around*|(|<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>\<less\><around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>|)>>

  <subsubsection|<samp|min> (unsigned)>

  \;

  <math|<rep|<text|<samp|'min'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|min>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|1\<leq\>n>

  \;

  Properties:

  <math|z\<leq\><around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|'min'>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|\<rceil\>><rsub|2<rsup|n>>>
  if and only if <math|z\<leq\><around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>>
  and <math|z\<leq\><around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>>

  \;

  Aliases:

  <math|<text|<samp|min>><rsub|1> \<assign\> <text|<samp|and>><rsub|1>
  :<2>\<times\><2>\<vdash\><2>>

  <subsubsection|<samp|max> (unsigned)>

  \;

  <math|<rep|<text|<samp|'max'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|max>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|1\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|max>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|\<rceil\>><rsub|2<rsup|n>>\<leq\>z>
  if and only if <math|<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>\<leq\>z>
  and <math|<around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>\<leq\>z>

  \;

  Aliases:

  <math|<text|<samp|max>><rsub|1> \<assign\> <text|<samp|or>><rsub|1>
  :<2>\<times\><2>\<vdash\><2>>

  <subsubsection|<samp|median> (unsigned)>

  \;

  <math|<rep|<text|<samp|'median'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|median>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><around*|(|<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>|)>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|1\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|min>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x<rsub|i>,x<rsub|j>|\<rangle\>>|\<rceil\>><rsub|2<rsup|n>>\<leq\><around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|median>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x<rsub|1>,<around*|\<langle\>|x<rsub|2>,x<rsub|3>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2<rsup|n>>\<leq\><around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|max>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x<rsub|i>,x<rsub|j>|\<rangle\>>|\<rceil\>><rsub|2<rsup|n>>>
  for all <math|1\<leq\>i\<less\>j\<leq\>3>.

  \;

  Aliases:

  <math|<text|<samp|median>><rsub|1> \<assign\> <text|<samp|maj>><rsub|1>
  :<2>\<times\><around*|(|<2>\<times\><2>|)>\<vdash\><2>>

  \;

  <subsubsection|<samp|div2n1n>>

  (Note: helper function for <samp|divmod>. See <hlink|Fast recursive
  division|http://cr.yp.to/bib/1998/burnikel.ps> by Bunikel and Ziegler
  (1998).)

  <math|<rep|<text|<samp|'div2n1n'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|div2n1n>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n+1>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  When <math|2<rsup|n-1>\<leq\><around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>
  >and<math|<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n+1>>\<less\>2<rsup|n>\<cdot\><around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>>,

  <\enumerate-alpha>
    <item><math|<around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>\<cdot\><around*|\<lceil\>|\<pi\><rsub|1><around*|(|<around*|\<llbracket\>|<text|<samp|div2n1n>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|\<rceil\>><rsub|2<rsup|n>>=<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n+1>>-<around*|\<lceil\>|\<pi\><rsub|2><around*|(|<around*|\<llbracket\>|<text|<samp|div2n1n>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|\<rceil\>><rsub|2<rsup|n>>>,
    and

    <item><math|<around*|\<lceil\>|\<pi\><rsub|2><around*|(|<around*|\<llbracket\>|<text|<samp|div2n1n>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|\<rceil\>><rsub|2<rsup|n>>\<less\><around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>>.
  </enumerate-alpha>

  \;

  When <math|2<rsup|n-1>\<gtr\><around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>
  >or<math|<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n+1>>\<geqslant\>2<rsup|n>\<cdot\><around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>>,
  then <math|bit<rsub|2<rsup|2n>,i><around*|(|<around*|\<llbracket\>|<text|<samp|div2n1n>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>=1>.

  \;

  <subsubsection|<samp|div-mod> (unsigned)>

  \;

  <math|<rep|<text|<samp|'div-mod'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|div-mod>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>\<cdot\><around*|\<lceil\>|\<pi\><rsub|1><around*|(|<around*|\<llbracket\>|<text|<samp|div-mod>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|\<rceil\>><rsub|2<rsup|n>>=<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>-<around*|\<lceil\>|\<pi\><rsub|2><around*|(|<around*|\<llbracket\>|<text|<samp|div-mod>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|\<rceil\>><rsub|2<rsup|n>>>

  \;

  For all <math|r\<in\>\<bbb-N\>> such that
  <math|<around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>\|<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>-r>
  we have<math|<around*|\<lceil\>|\<pi\><rsub|2><around*|(|<around*|\<llbracket\>|<text|<samp|div-mod>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|)>|\<rceil\>><rsub|2<rsup|n>>\<leq\>r>.

  <subsubsection|<samp|divide> (unsigned)>

  \;

  <math|<rep|<text|<samp|'divide'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|divide>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  <subsubsection|<samp|modulo> (unsigned)>

  \;

  <math|<rep|<text|<samp|'modulo'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|modulo>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  <subsubsection|<samp|divides> (unsigned)>

  \;

  <math|<rep|<text|<samp|'divides'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|divides>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2>> for
  <math|0\<leq\>n>

  \;

  Properties:

  <math|<around*|\<lceil\>|<around*|\<llbracket\>|<text|<samp|divides>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>|\<rceil\>><rsub|1>=\<chi\><around*|(|<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>\|<around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>|)>>

  <subsubsection|<samp|eea> (unsigned)>

  \;

  <math|<rep|<text|<samp|'eea'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|eea>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><around*|(|<around*|(|<around*|(|<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>|)>+<around*|(|<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>|)>|)>\<times\><around*|(|<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>|)>|)>\<times\><2><rsup|2<rsup|n>>>
  for <math|0\<leq\>n>

  \;

  Properties:

  Let <math|<around*|\<langle\>|<around*|\<langle\>|b,<around*|\<langle\>|c<rsub|y>,c<rsub|x>|\<rangle\>>|\<rangle\>>,d|\<rangle\>>\<assign\><around*|\<llbracket\>|<text|<samp|eea>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|x,y|\<rangle\>>>

  \;

  <math|<around*|\<lceil\>|c<rsub|x>|\<rceil\>><rsub|2<rsup|n>>*<around*|\<lceil\>|d|\<rceil\>><rsub|2<rsup|n>>=<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>>

  <math|<around*|\<lceil\>|c<rsub|y>|\<rceil\>><rsub|2<rsup|n>>*<around*|\<lceil\>|d|\<rceil\>><rsub|2<rsup|n>>=<around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>>

  \;

  If <math|<injl|<around*|\<langle\>|s,t|\<rangle\>>>=b> then
  <math|<around*|\<lceil\>|s|\<rceil\>><rsub|2<rsup|n>>*<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>-<around*|\<lceil\>|t|\<rceil\>><rsub|2<rsup|n>>*<around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>=<around*|\<lceil\>|d|\<rceil\>><rsub|2<rsup|n>>>
  and either <math|<around*|\<lceil\>|s|\<rceil\>><rsub|2<rsup|n>>*\<less\><frac|<around*|\<lceil\>|c<rsub|y>|\<rceil\>><rsub|2<rsup|n>>|2>>
  or <math|<around*|\<lceil\>|t|\<rceil\>><rsub|2<rsup|n>>*\<less\><frac|<around*|\<lceil\>|c<rsub|x>|\<rceil\>><rsub|2<rsup|n>>|2>>.

  If <math|<injr|<around*|\<langle\>|s,t|\<rangle\>>>=b> then
  <math|<around*|\<lceil\>|s|\<rceil\>><rsub|2<rsup|n>>*<around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|n>>-<around*|\<lceil\>|t|\<rceil\>><rsub|2<rsup|n>>*<around*|\<lceil\>|y|\<rceil\>><rsub|2<rsup|n>>=-<around*|\<lceil\>|d|\<rceil\>><rsub|2<rsup|n>>>
  and either <math|<around*|\<lceil\>|s|\<rceil\>><rsub|2<rsup|n>>*\<less\><frac|<around*|\<lceil\>|c<rsub|y>|\<rceil\>><rsub|2<rsup|n>>|2>>
  or <math|<around*|\<lceil\>|t|\<rceil\>><rsub|2<rsup|n>>*\<less\><frac|<around*|\<lceil\>|c<rsub|x>|\<rceil\>><rsub|2<rsup|n>>|2>.>

  \;

  <math|<around*|\<llbracket\>|<text|<samp|eea>><rsub|2<rsup|n>>|\<rrbracket\>><around*|\<langle\>|<around*|\<lfloor\>|x|\<rfloor\>>,<around*|\<lfloor\>|x|\<rfloor\>>|\<rangle\>>=<around*|\<langle\>|<around*|\<langle\>|<injl|<around*|\<langle\>|<around*|\<lfloor\>|1|\<rfloor\>>,<around*|\<lfloor\>|0|\<rfloor\>>|\<rangle\>>>,<around*|\<langle\>|<around*|\<lfloor\>|1|\<rfloor\>>,<around*|\<lfloor\>|1|\<rfloor\>>|\<rangle\>>|\<rangle\>>,<around*|\<lfloor\>|x|\<rfloor\>>|\<rangle\>>>.

  <subsubsection|<samp|bezout> (unsigned)>

  (CAUTION: Not defined when <math|n\<leq\>1>.)

  <math|<rep|<text|<samp|'bezout'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|bezout>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><around*|(|<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>|)>+<around*|(|<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>|)>>
  for <math|1\<leq\>n>

  <subsubsection|<samp|gcd> (unsigned)>

  (CAUTION: Not defined when <math|n\<leq\>1>.)

  <math|<rep|<text|<samp|'gcd'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|gcd>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>>
  for <math|1\<leq\>n>

  <subsubsection|<samp|cofactors> (unsigned)>

  (CAUTION: Not defined when <math|n\<leq\>1>.)

  <math|<rep|<text|<samp|'cofactors'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|cofactors>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>>
  for <math|1\<leq\>n>

  <subsubsection|<samp|lcm> (unsigned)>

  \;

  <math|<rep|<text|<samp|'lcm'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|lcm>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n+1>>>
  for <math|0\<leq\>n>

  <subsubsection|<samp|jacobi> (unsigned)>

  \;

  <math|<rep|<text|<samp|'jacobi'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|jacobi>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2><rsup|2>> for
  <math|0\<leq\>n>

  <subsubsection|<samp|absolute-value> (signed input/unsigned output)>

  \;

  <math|<rep|<text|<samp|'absolute-value'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>>

  <math|<text|<samp|absolute-value>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2<rsup|n>>> for <math|0\<leq\>n>

  <subsubsection|<verbatim|><samp|sign>>

  (CAUTION: Not defined when <math|n=0>. See Aliases.)

  <\math>
    <rep|<text|<samp|'sign'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n|>
  </math>

  <math|<text|<samp|sign>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<vdash\><2><rsup|2>> for <math|1\<leq\>n>

  \;

  Properties:

  <math|<around*|\<llbracket\>|<text|<samp|sign>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>=<around*|\<langle\>|<around*|\<llbracket\>|<text|<samp|leftmost>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>,<around*|\<llbracket\>|<text|<samp|some>><rsub|2<rsup|n>>|\<rrbracket\>><around*|(|x|)>|\<rangle\>>>

  <subsubsection|<samp|signed-le>>

  \;

  <math|<rep|<text|<samp|'signed-le'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|signed-le>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2>> for
  <math|0\<leq\>n>

  <subsubsection|<samp|signed-lt>>

  \;

  <math|<rep|<text|<samp|'signed-lt'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|n+1|>>

  <math|<text|<samp|signed-lt>><rsub|2<rsup|n>>
  :<2><rsup|2<rsup|n>>\<times\><2><rsup|2<rsup|n>>\<vdash\><2>> for
  <math|0\<leq\>n>

  <subsubsection|<samp|signed-min>>

  <subsubsection|<samp|signed-max>>

  <subsubsection|<samp|signed-median>>

  <subsubsection|<samp|signed-right-shift>>

  Right shift by a signed amount with sign extension. Negative values are a
  left shift.

  <subsubsection|<samp|signed-divmod> (unsigned denominator)>

  <subsubsection|<samp|signed-div> (unsigned denominator)>

  <subsubsection|<samp|signed-signed-divmod> (signed denominator)>

  <subsubsection|<samp|signed-signed-div> (signed denominator)>

  \;

  <subsection|<verbatim|110101...: >Jets for hash functions>

  <subsubsection|<verbatim|1101010...: >Jets for SHA-2>

  <paragraph|<samp|sha-256-block>>

  \;

  <math|<rep|<text|<samp|'sha-256-block'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>>

  <math|<text|<samp|sha-256-block>> :<2><rsup|256>\<times\><2><rsup|512>\<vdash\><2><rsup|256>>

  \;

  <paragraph|<samp|sha-256-iv>>

  \;

  <math|<rep|<text|<samp|'sha-256-iv'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>>

  <\math>
    <text|<samp|sha-256-iv>> :<1>\<vdash\><2><rsup|256>
  </math>

  <subsubsection|<verbatim|110101100...: >Jets for SHA-3>

  In this section we define <math|X<rsup|5>\<assign\>X\<times\>X<rsup|4>> and
  <math|X<rsup|1600>\<assign\><around*|(|<around*|(|X<rsup|64>|)><rsup|5>|)><rsup|5>>.

  \;

  <paragraph|<samp|sha3-zero>>

  \;

  <\math>
    <rep|<text|<samp|'sha3-zero'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|sha3-zero>> :<1>\<vdash\><2><rsup|1600>>

  \;

  <paragraph|<samp|sha3-absorb>>

  (Note: we should proably byte-stwap the input before xoring it into place

  <\math>
    <rep|<text|<samp|'sha3-absorb'>><rsub|n,m>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>\<cdummy\><rep|n|>\<cdummy\><rep|m|>
  </math>

  <math|<text|<samp|sha3-absorb>><rsub|n,m>:<2><rsup|64>\<times\><2><rsup|1600>\<vdash\><2><rsup|1600>>
  for <math|1\<leq\>n,m\<leq\>5>

  \;

  <paragraph|<samp|sha3-xor>>

  \;

  <\math>
    <rep|<text|<samp|'sha3-xor'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|sha3-xor>> :<2><rsup|1600>\<times\><2><rsup|1600>\<vdash\><2><rsup|1600>>

  \;

  <paragraph|<samp|sha3-permute>>

  \;

  <\math>
    <rep|<text|<samp|'sha3-permute'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|sha3-permute>>:<2><rsup|1600>\<vdash\><2><rsup|1600>>

  \;

  <paragraph|<samp|sha3-squeeze-256>>

  \;

  <\math>
    <rep|<text|<samp|'sha3-squeeze-256'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|sha3-squeeze-256>>:<2><rsup|1600>\<vdash\><2><rsup|256>>

  \;

  <paragraph|<samp|sha3-squeeze-512>>

  \;

  <\math>
    <rep|<text|<samp|'sha3-squeeze-512'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|sha3-squeeze-512>>:<2><rsup|1600>\<vdash\><2><rsup|512>>

  <subsubsection|<verbatim|110101101...: >Jets for RIPEMD>

  <subsubsection|<verbatim|110101110000...: >Jets for SHA-1 (RESERVED)>

  <subsection|<verbatim|110110000...: >Jets for elliptic curve functions>

  <subsubsection|<verbatim|1101100000...: >Jets for secp256k1>

  In this section we define <math|Scalar\<assign\><2><rsup|256>>,
  <math|<2><rsup|129>\<assign\><2>\<times\><2><rsup|128>>,
  <math|FE\<assign\><2><rsup|256>>, <math|GE\<assign\>FE\<times\>FE>, and
  <math|GEJ\<assign\>GE\<times\>FE>, <math|Point\<assign\><2>\<times\>FE>.

  (Note: To convert GE to GEJ pair with <samp|one>).

  <with|color|red|TODO: Verify that all <em|equivalent> FE and Scalar inputs
  yield <em|equal> outputs.>

  \;

  <paragraph|<samp|secp256k1-point-verify>>

  (Note: Support only recommened up to <math|2<rsup|n>\<leq\><with|color|red|TODO
  8?>>.)

  <\math>
    <rep|<text|<samp|'secp256k1-point-verify'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>\<cdummy\><rep|n+1|>
  </math>

  <math|<text|<samp|secp256k1-point-verify>><rsub|2<rsup|n>>:<around*|(|<around*|(|Scalar\<times\>Point|)><rsup|2<rsup|n>>\<times\>Scalar|)>\<times\>Point\<vdash\><1>>
  for <math|0\<leq\>n>

  \;

  <paragraph|<samp|secp256k1-decompress>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-decompress'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>\<cdummy\><rep|n+1|>
  </math>

  <math|<text|<samp|secp256k1-decompress>>:Point\<vdash\><maybe><around*|(|GE|)>>
  for <math|0\<leq\>n>

  \;

  <paragraph|<samp|secp256k1-linear-verify>>

  (Note: Support only recommened up to <math|2<rsup|n>\<leq\><with|color|red|TODO
  8?>>.)

  <\math>
    <rep|<text|<samp|'secp256k1-linear-verify'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>\<cdummy\><rep|n+1|>
  </math>

  <math|<text|<samp|secp256k1-linear-verify>><rsub|2<rsup|n>>:<around*|(|<around*|(|Scalar\<times\>GE|)><rsup|2<rsup|n>>\<times\>Scalar|)>\<times\>GE\<vdash\><1>>
  for <math|0\<leq\>n>

  \;

  <paragraph|<samp|secp256k1-linear-combination>>

  (Note: Support only recommened up to <math|2<rsup|n>\<leq\><with|color|red|TODO
  8?>>.)

  <\math>
    <rep|<text|<samp|'secp256k1-linear-combination'>><rsub|2<rsup|n>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>\<cdummy\><rep|n+1|>
  </math>

  <math|<text|<samp|secp256k1-linear-combination>><rsub|2<rsup|n>>:<around*|(|Scalar\<times\>GEJ|)><rsup|2<rsup|n>>\<times\>Scalar\<vdash\>GEJ>
  for <math|0\<leq\>n>

  \;

  <paragraph|<samp|secp256k1-scale>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-scale'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-scale>>:Scalar\<times\>GEJ\<vdash\>GEJ>

  \;

  <paragraph|<samp|secp256k1-generate>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-generate'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-generate>>:Scalar\<vdash\>GEJ>

  \;

  <paragraph|<samp|secp256k1-gej-infinity>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-infinity'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-infinity>>:<1>\<vdash\>GEJ>

  \;

  <paragraph|<samp|secp256k1-gej-normalize>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-normalize'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-normalize>>:GEJ\<vdash\>GE>

  \;

  Returns <math|<around*|(|0,0|)>> when passed infinity.

  \;

  <paragraph|<samp|secp256k1-gej-negate>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-negate'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-negate>>:GEJ\<vdash\>GEJ>

  \;

  <paragraph|<samp|secp256k1-ge-negate>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-ge-negate'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-ge-negate>>:GE\<vdash\>GE>

  \;

  <paragraph|<samp|secp256k1-gej-double>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-double'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-double>>:GEJ\<vdash\>GEJ>

  \;

  <paragraph|<samp|secp256k1-gej-add>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-add'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-add>>:GEJ\<times\>GEJ\<vdash\>GEJ>

  \;

  <paragraph|<samp|secp256k1-gej-ge-add-ex>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-ge-add-ex'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-ge-add-ex>>:GEJ\<times\>GE\<vdash\>FE\<times\>GEJ>

  \;

  <paragraph|<samp|secp256k1-gej-ge-add>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-ge-add'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-ge-add>>:GEJ\<times\>GE\<vdash\>GEJ>

  \;

  <paragraph|<samp|secp256k1-gej-rescale>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-rescale'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-rescale>>:GEJ\<times\>FE\<vdash\>GEJ>

  \;

  <paragraph|<samp|secp256k1-gej-is-infinity>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-is-infinity'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-is-infinity>>:GEJ\<vdash\><2>>

  \;

  <paragraph|<samp|secp256k1-gej-equiv> <with|color|red|Does not exist in
  libsecp256k1>>

  <with|color|red|Warning: this can be implemented by comparing coordinates
  (by cross multiplication) or by adding points and testing for infinity.
  \ However these two implementations yeilds different results for off curve
  points.>

  <\math>
    <rep|<text|<samp|'secp256k1-gej-equiv'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-equiv>>:GEJ\<times\>GEJ\<vdash\><2>>

  \;

  <paragraph|<samp|secp256k1-gej-ge-equiv> <with|color|red|Does not exist in
  libsecp256k1>>

  <with|color|red|Warning: this can be implemented by comparing coordinates
  (by cross multiplication) or by adding points and testing for infinity.
  \ However these two implementations yeilds different results for off curve
  points.>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-ge-equiv'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-ge-equiv>>:GEJ\<times\>GE\<vdash\><2>>

  \;

  <paragraph|<samp|secp256k1-gej-x-equiv>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-x-equiv'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-x-equiv>>:FE\<times\>GEJ\<vdash\><2>>

  \;

  <paragraph|<samp|secp256k1-gej-y-is-odd>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-y-is-odd'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-y-is-odd>>:GEJ\<vdash\><2>>

  \;

  <paragraph|<samp|secp256k1-gej-is-on-curve>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-is-on-curve'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-is-on-curve>>:GEJ\<vdash\><2>>

  \;

  <paragraph|<samp|secp256k1-ge-is-on-curve>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-ge-is-on-curve'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-ge-is-on-curve>>:GEJ\<vdash\><2>>

  \;

  <paragraph|<samp|secp256k1-scalar-normalize>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-scalar-normalize'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-scalar-normalize>>:Scalar\<vdash\>Scalar>

  \;

  <paragraph|<samp|secp256k1-scalar-negate>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-scalar-negate'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|'secp256k1-scalar-negate'>>:Scalar\<vdash\>Scalar>

  \;

  <paragraph|<samp|secp256k1-scalar-add>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-scalar-add'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-scalar-add>>:Scalar\<times\>Scalar\<vdash\>Scalar>

  \;

  <paragraph|<samp|secp256k1-scalar-square>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-scalar-square'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-scalar-square>>:Scalar\<vdash\>Scalar>

  \;

  <paragraph|<samp|secp256k1-scalar-multiply>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-scalar-multiply'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-scalar-multiply>>:Scalar\<times\>Scalar\<vdash\>Scalar>

  \;

  <paragraph|<samp|secp256k1-scalar-multiply-lambda>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-scalar-multiply-lambda'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-scalar-multiply-lambda>>:Scalar\<vdash\>Scalar>

  \;

  <paragraph|<samp|secp256k1-scalar-invert>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-scalar-invert'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-scalar-invert>>:Scalar\<vdash\>Scalar>

  \;

  <paragraph|<samp|secp256k1-scalar-is-zero>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-scalar-is-zero'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-scalar-is-zero>>:Scalar\<vdash\><2>>

  \;

  <paragraph|<samp|secp256k1-ge-scale-lambda>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-ge-scale-lambda'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-ge-scale-lambda>>:GE\<vdash\>GE>

  \;

  <paragraph|<samp|secp256k1-gej-scale-lambda> <with|color|red|Consider
  removing>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-gej-scale-lambda'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-gej-scale-lambda>>:GEJ\<vdash\>GEJ>

  \;

  <paragraph|<samp|secp256k1-scalar-split-lambda>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-scalar-split-lambda'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-scalar-split-lambda>>:Scalar\<vdash\><2><rsup|129>\<times\><2><rsup|129>>

  \;

  <\with|color|red>
    TODO Properties:

    <math|\<lambda\>\<cdot\><around*|\<lceil\>|\<pi\><rsub|1><around*|(|<around*|\<llbracket\>|<text|<samp|'secp256k1-scalar-split'>>|\<rrbracket\>><around*|(|x|)>|)>|\<rceil\>><rsub|2<rsup|128>>+<around*|\<lceil\>|\<pi\><rsub|2><around*|(|<around*|\<llbracket\>|<text|<samp|'secp256k1-scalar-split'>>|\<rrbracket\>><around*|(|x|)>|)>|\<rceil\>><rsub|2<rsup|128>>\<equiv\><rsub|Scalar><around*|\<lceil\>|x|\<rceil\>><rsub|2<rsup|256>>>
  </with>

  \;

  <paragraph|<samp|secp256k1-short-scalar>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-short-scalar'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-short-scalar>>:<2><rsup|129>\<vdash\>Scalar>

  \;

  <paragraph|<samp|secp256k1-fe-normalize>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-fe-normalize'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-fe-normalize>>:FE\<vdash\>FE>

  \;

  <paragraph|<samp|secp256k1-fe-negate>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-fe-negate'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-fe-negate>>:FE\<vdash\>FE>

  \;

  <paragraph|<samp|secp256k1-fe-add>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-fe-negate'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-fe-negate>>:FE\<times\>FE\<vdash\>FE>

  \;

  <paragraph|<samp|secp256k1-fe-square>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-fe-square'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-fe-square>>:FE\<vdash\>FE>

  \;

  <paragraph|<samp|secp256k1-fe-multiply>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-fe-multiply'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-fe-multiply>>:FE\<times\>FE\<vdash\>FE>

  \;

  <paragraph|<samp|secp256k1-fe-multiply-beta>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-fe-multiply-beta'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-fe-multiply-beta>>:FE\<vdash\>FE>

  \;

  <paragraph|<samp|secp256k1-fe-invert>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-fe-invert'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  gi<math|<text|<samp|secp256k1-fe-invert>>:FE\<vdash\>FE>

  \;

  <paragraph|<samp|secp256k1-fe-square-root>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-fe-square-root'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-fe-square-root>>:FE\<vdash\><maybe><around*|(|FE|)>>

  \;

  <paragraph|<samp|secp256k1-fe-is-zero>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-fe-is-zero'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-fe-is-zero>>:FE\<vdash\><2>>

  \;

  <paragraph|<samp|secp256k1-fe-is-odd>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-fe-is-odd'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-fe-is-odd>>:FE\<vdash\><2>>

  \;

  <paragraph|<samp|secp256k1-fe-is-quad>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-fe-is-quad'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-fe-is-quad>>:FE\<vdash\><2>>

  <subsection|<verbatim|110110001...: >Jets for digital signatures>

  <subsubsection|<verbatim|1101100010...: >Jets for secp256k1 based digital
  signatures>

  In this section we define <math|Pubkey\<assign\><2><rsup|256>>,
  <math|Signature\<assign\><2><rsup|512>>.

  \;

  <paragraph|<samp|bip0340-schnorr-verify>>

  (Note: this jet can fail.)

  <\math>
    <rep|<text|<samp|'bip0340-schnorr-verify'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|bip0340-schnorr-verify>>:<around*|(|Pubkey\<times\><2><rsup|256>|)>\<times\>Signature\<vdash\><1>>

  \;

  <paragraph|<samp|bip0340-challenge-iv>>

  \;

  <\math>
    <rep|<text|<samp|'bip0340-challenge-iv'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|bip0340-challenge-iv>>:<1>\<vdash\><2><rsup|256>>

  \;

  <paragraph|<samp|bip0340-challenge-midstate>>

  \;

  <\math>
    <rep|<text|<samp|'bip0340-challenge-midstate'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <\math>
    <text|<samp|bip0340-challenge-midstate>>:FE\<times\>Pubkey\<vdash\><2><rsup|256>
  </math>

  \;

  <paragraph|<samp|secp256k1-signature-unpack>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-signtaure-unpack'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-signature-unpack>>:Signature\<vdash\><maybe><around*|(|FE\<times\>Scalar|)>>

  \;

  <paragraph|<samp|secp256k1-pubkey-unpack>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-pubkey-unpack'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-pubkey-unpack>>:Pubkey\<vdash\><maybe><around*|(|GE|)>>

  \;

  <paragraph|<samp|secp256k1-pubkey-unpack-neg>>

  \;

  <\math>
    <rep|<text|<samp|'secp256k1-pubkey-unpack-neg'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|secp256k1-pubkey-unpack-neg>>:Pubkey\<vdash\><maybe><around*|(|GE|)>>

  \;

  <paragraph|<samp|secp256k1-ecdsa>>

  \;

  <subsection|<verbatim|110110010...: >Jets for Simplicity>

  Tagged hash IVs for basic simplicity combinators, signature hashes, etc.
  The CMR of various expressions for constants.

  \;

  These would be use for Simplicity covenants.

  <subsubsection|<verbatim|11011000100...: >Jets for tagged hash IVs>

  <paragraph|<samp|iden-commitment-tag>>

  <paragraph|<samp|comp-commitment-tag>>

  <paragraph|<samp|unit-commitment-tag>>

  <paragraph|<samp|injl-commitment-tag>>

  <paragraph|<samp|injr-commitment-tag>>

  <paragraph|<samp|case-commitment-tag>>

  <paragraph|<samp|pair-commitment-tag>>

  <paragraph|<samp|take-commitment-tag>>

  <paragraph|<samp|drop-commitment-tag>>

  <paragraph|<samp|witness-commitment-tag>>

  <paragraph|<samp|disconnect-commitment-tag>>

  <paragraph|<samp|fail-commitment-tag>>

  <paragraph|<samp|signtaure-tag>>

  \;

  <\math>
    <rep|<text|<samp|'signature-tag'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>\<cdummy\><rep|<value|paragraph-nr>|>
  </math>

  <math|<text|<samp|signature-tag>>:<1>\<vdash\><2><rsup|256>>

  \;

  <paragraph|<samp|sighash-tag>>

  <subsection|<verbatim|110110011...: >Jets for Bitcoin (without primitives)>

  This section is not recommended for non-Bitcoin(-like) applications.

  \;

  In this section we define <math|Height\<assign\><2><rsup|32>>,
  <math|Time\<assign\><2><rsup|32>>, <math|Distance\<assign\><2><rsup|16>>,
  and <math|Duration = <2><rsup|32>>.

  <subsubsection|<samp|parse-lock>>

  (Note: <math|<around*|\<llbracket\>|<text|<samp|'parse-lock'>>|\<rrbracket\>><around*|\<lfloor\>|0|\<rfloor\>><rsub|32>\<assign\><injl|<around*|(|0|)>>>)

  <math|<rep|<text|<samp|'parse-lock'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|parse-lock>> :<2><rsup|32>\<vdash\>Height+Time>

  <subsubsection|<samp|parse-sequence>>

  \;

  <math|<rep|<text|<samp|'parse-sequence'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|parse-sequence>> :<2><rsup|32>\<vdash\><maybe><around*|(|Distance+Duration|)>>

  <subsection|<verbatim|1101101000...: >Jets for Elements (without
  primitives)>

  This section is not recommended for non-Elements applications.

  <subsubsection|<samp|generate-entropy>>

  \;

  <math|<rep|<text|<samp|'generate-entropy'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|generate-entropy>> :Outpoint\<times\><2><rsup|256>\<vdash\><2><rsup|256>>

  <subsubsection|<samp|calculate-asset>>

  \;

  <math|<rep|<text|<samp|'calculate-asset'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|calculate-asset>> :<2><rsup|256>\<vdash\>ExplicitAsset>

  <subsubsection|<samp|calculate-token>>

  \;

  <math|<rep|<text|<samp|'calculate-token'>>|>\<assign\><verbatim|<around*|[|110|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|calculate-token>> :<2>\<times\><2><rsup|256>\<vdash\>ExplicitAsset>

  <section|<verbatim|111...: >Bitcoin Jets>

  <subsection|Transaction>

  <\itemize>
    <item><math|<text|<samp|total-fee>>\<of\><1>\<vdash\>Value>
  </itemize>

  <subsection|Signature Hash Modes>

  <\itemize>
    <item><math|<text|<samp|sighash-all>>\<of\><1>\<vdash\><2><rsup|256>>

    <item><math|<text|<samp|sighash-single>>\<of\><1>\<vdash\><2><rsup|256>>
    (anyone can pay)

    <item><math|<text|<samp|sighash-outputs>>\<of\>Index\<times\><2><rsup|32>\<vdash\><2><rsup|256>>
    (anyone can pay)
  </itemize>

  <subsection|Time Locks>

  In this section we define <math|Height\<assign\><2><rsup|32>>,
  <math|Time\<assign\><2><rsup|32>>, <math|Distance\<assign\><2><rsup|16>>,
  and <math|Duration = <2><rsup|32>>.

  <subsubsection|<samp|total-height-lock>>

  \;

  <math|<rep|<text|<samp|'total-height-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|<samp|total-height-lock>>>
  :<1>\<vdash\><maybe><around*|(|Height|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> when <samp|is-final> returns
  <math|<math-tt|1><rsub|<2>>> and <math|<around*|\<llbracket\>|<text|<samp|parse-lock>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|lockTime>>|\<rrbracket\>>>
  returns <math|<injl|<around*|(|x|)>>>.

  <subsubsection|<samp|total-time-lock>>

  \;

  <math|<rep|<text|<samp|'total-time-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|total-time-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Time|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> when <samp|is-final> returns
  <math|<math-tt|1><rsub|<2>>> and <math|<around*|\<llbracket\>|<text|<samp|parse-lock>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|lockTime>>|\<rrbracket\>>>
  returns <math|<injr|<around*|(|x|)>>>.

  <subsubsection|<samp|total-distance-lock>>

  \;

  <math|<rep|<text|<samp|'total-distance-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|total-distance-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Distance|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> where <math|x> is the largest
  among the <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  returned by <samp|input-distance-lock> on any inputs, if any such values
  are returned.

  <subsubsection|<samp|total-duration-lock>>

  \;

  <math|<rep|<text|<samp|'total-duration-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|total-duration-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Duration|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> where <math|x> is the largest
  among the <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  returned by <samp|input-duration-lock> on any inputs, if any such values
  are returned.

  <subsubsection|<samp|is-final>>

  \;

  <math|<rep|<text|<samp|'is-final'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|is-final>'>> :<1>\<vdash\><2>>

  \;

  Returns <math|<math-tt|1><rsub|<2>>> when <samp|input-is-final> returns
  <math|\<eta\><rsup|S><around*|(|<math-tt|1><rsub|<2>>|)>> for all inputs.

  <subsubsection|<samp|current-height-lock>>

  \;

  <math|<rep|<text|<samp|'current-height-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|current-height-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Height|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> when <samp|current-is-final>
  returns <math|<math-tt|1><rsub|<2>>> and
  <math|<around*|\<llbracket\>|<text|<samp|parse-lock>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|lockTime>>|\<rrbracket\>>>
  returns <math|<injl|<around*|(|x|)>>>.

  <subsubsection|<samp|current-time-lock>>

  \;

  <math|<rep|<text|<samp|'current-time-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|current-time-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Time|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> when <samp|current-is-final>
  returns <math|<math-tt|1><rsub|<2>>> and
  <math|<around*|\<llbracket\>|<text|<samp|parse-lock>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|lockTime>>|\<rrbracket\>>>
  returns <math|<injr|<around*|(|x|)>>>.

  <subsubsection|<samp|current-distance-lock>>

  \;

  <math|<rep|<text|<samp|'current-distance-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|current-distance-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Distance|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> when
  <math|<around*|\<llbracket\>|<text|<samp|parse-sequence>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|currentSequence>>|\<rrbracket\>>>
  returns <math|<injl|<around*|(|x|)>>>.

  <subsubsection|<samp|current-duration-lock>>

  \;

  <math|<rep|<text|<samp|'current-duration-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|current-duration-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Duration|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  when <math|<around*|\<llbracket\>|<text|<samp|parse-sequence>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|currentSequence>>|\<rrbracket\>>>
  returns <math|<injr|<around*|(|x|)>>>.

  <subsubsection|<samp|current-is-Final>>

  \;

  <math|<rep|<text|<samp|'current-is-final'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|current-is-final>'>> :<1>\<vdash\><2>>

  \;

  Returns <math-tt|1><rsub|<2>> when <math|<around*|\<llbracket\>|<text|<samp|<math|currentSequence>>>|\<rrbracket\>>>
  returns <math|<around*|\<lfloor\>|2<rsup|32>-1|\<rfloor\>>>.

  <subsubsection|<samp|input-height-lock>>

  \;

  <math|<rep|<text|<samp|'input-height-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|input-height-lock>'>>
  :Index\<vdash\><maybe><around*|(|<maybe><around*|(|Height|)>|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  when <samp|input-is-final> returns <math|\<eta\><rsup|S><around*|(|<math-tt|1><rsub|<2>>|)>>
  and <math|<around*|\<llbracket\>|<text|<samp|parse-lock>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|lockTime>>|\<rrbracket\>>>
  returns <math|<injl|<around*|(|x|)>>>.

  Returns <math|\<emptyset\><rsup|<maybe>>> when the input index is out of
  range.

  <subsubsection|<samp|input-time-lock>>

  \;

  <math|<rep|<text|<samp|'input-time-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|input-time-lock>'>>
  :Index\<vdash\><maybe><around*|(|<maybe><around*|(|Time|)>|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  when <samp|input-is-final> returns <math|\<eta\><rsup|S><around*|(|<math-tt|1><rsub|<2>>|)>>
  and <math|<around*|\<llbracket\>|<text|<samp|parse-lock>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|lockTime>>|\<rrbracket\>>>
  returns <math|<injr|<around*|(|x|)>>>.

  Returns <math|\<emptyset\><rsup|<maybe>>> when the input index is out of
  range.

  <subsubsection|<samp|input-distance-lock>>

  \;

  <math|<rep|<text|<samp|'input-distance-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|input-distance-lock>'>>
  :Index\<vdash\><maybe><around*|(|<maybe><around*|(|Distance|)>|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  when <math|<maybe><around*|\<llbracket\>|<text|<samp|parse-sequence>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|inputSequence>>|\<rrbracket\>>>
  returns <math|\<eta\><rsup|S><around*|(|<injl|<around*|(|x|)>>|)>>.

  Returns <math|\<emptyset\><rsup|<maybe>>> when the input index is out of
  range.

  <subsubsection|<samp|input-duration-lock>>

  \;

  <math|<rep|<text|<samp|'input-duration-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|input-duration-lock>'>>
  :Index\<vdash\><maybe><around*|(|<maybe><around*|(|Duration|)>|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  when <math|<maybe><around*|\<llbracket\>|<text|<samp|parse-sequence>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|inputSequence>>|\<rrbracket\>>>
  returns <math|\<eta\><rsup|S><around*|(|<injr|<around*|(|x|)>>|)>>.

  Returns <math|\<emptyset\><rsup|<maybe>>> when the input index is out of
  range.

  <subsubsection|<samp|input-is-final>>

  \;

  <math|<rep|<text|<samp|'input-is-final'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|input-is-final>'>>
  :Index\<vdash\><maybe><around*|(|<2>|)>>

  \;

  Returns \<eta\><rsup|S><around*|(|<math-tt|1><rsub|<2>>|)> when
  <math|<around*|\<llbracket\>|<text|<samp|<math|inputSequence>>>|\<rrbracket\>>>
  returns \<eta\><rsup|S><around*|(|<math|<around*|\<lfloor\>|2<rsup|32>-1|\<rfloor\>>>|)>.

  Returns <math|\<emptyset\><rsup|<maybe>>> when the input index is out of
  range.

  <em|><section|<verbatim|111...: >Elements Jets>

  <subsection|Transaction>

  <\itemize>
    <item><math|<text|<samp|'<samp|outputIsFee>'>>
    :Index\<vdash\><maybe><around*|(|<2>|)>>
  </itemize>

  <\itemize>
    <item><math|<samp|sigHashAll>\<of\><1>\<vdash\><2><rsup|256>>

    <item><math|<samp|sigHashSingle>\<of\><1>\<vdash\><2><rsup|256>> (anyone
    can pay)

    <item><math|<samp|sigHashOutputs>\<of\>Index\<times\><2><rsup|32>\<vdash\><2><rsup|256>>
    (anyone can pay)
  </itemize>

  <subsection|Time Locks>

  In this section we define <math|Height\<assign\><2><rsup|32>>,
  <math|Time\<assign\><2><rsup|32>>, <math|Distance\<assign\><2><rsup|16>>,
  and <math|Duration = <2><rsup|32>>.

  <subsubsection|<samp|total-height-lock>>

  \;

  <math|<rep|<text|<samp|'total-height-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|total-height-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Height|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> when <samp|is-final> returns
  <math|<math-tt|1><rsub|<2>>> and <math|<around*|\<llbracket\>|<text|<samp|parse-lock>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|lockTime>>|\<rrbracket\>>>
  returns <math|<injl|<around*|(|x|)>>>.

  <subsubsection|<samp|total-time-lock>>

  \;

  <math|<rep|<text|<samp|'total-time-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|total-time-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Time|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> when <samp|is-final> returns
  <math|<math-tt|1><rsub|<2>>> and <math|<around*|\<llbracket\>|<text|<samp|parse-lock>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|lockTime>>|\<rrbracket\>>>
  returns <math|<injr|<around*|(|x|)>>>.

  <subsubsection|<samp|total-distance-lock>>

  \;

  <math|<rep|<text|<samp|'total-distance-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|total-distance-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Distance|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> where <math|x> is the largest
  among the <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  returned by <samp|input-distance-lock> on any inputs, if any such values
  are returned.

  <subsubsection|<samp|total-duration-lock>>

  \;

  <math|<rep|<text|<samp|'total-duration-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|total-duration-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Duration|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> where <math|x> is the largest
  among the <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  returned by <samp|input-duration-lock> on any inputs, if any such values
  are returned.

  <subsubsection|<samp|is-final>>

  \;

  <math|<rep|<text|<samp|'is-final'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|is-final>'>> :<1>\<vdash\><2>>

  \;

  Returns <math|<math-tt|1><rsub|<2>>> when <samp|input-is-final> returns
  <math|\<eta\><rsup|S><around*|(|<math-tt|1><rsub|<2>>|)>> for all inputs.

  <subsubsection|<samp|current-height-lock>>

  \;

  <math|<rep|<text|<samp|'current-height-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|current-height-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Height|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> when <samp|current-is-final>
  returns <math|<math-tt|1><rsub|<2>>> and
  <math|<around*|\<llbracket\>|<text|<samp|parse-lock>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|lockTime>>|\<rrbracket\>>>
  returns <math|<injl|<around*|(|x|)>>>.

  <subsubsection|<samp|current-time-lock>>

  \;

  <math|<rep|<text|<samp|'current-time-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|current-time-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Time|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> when <samp|current-is-final>
  returns <math|<math-tt|1><rsub|<2>>> and
  <math|<around*|\<llbracket\>|<text|<samp|parse-lock>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|lockTime>>|\<rrbracket\>>>
  returns <math|<injr|<around*|(|x|)>>>.

  <subsubsection|<samp|current-distance-lock>>

  \;

  <math|<rep|<text|<samp|'current-distance-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|current-distance-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Distance|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|x|)>> when
  <math|<around*|\<llbracket\>|<text|<samp|parse-sequence>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|currentSequence>>|\<rrbracket\>>>
  returns <math|<injl|<around*|(|x|)>>>.

  <subsubsection|<samp|current-duration-lock>>

  \;

  <math|<rep|<text|<samp|'current-duration-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|current-duration-lock>'>>
  :<1>\<vdash\><maybe><around*|(|Duration|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  when <math|<around*|\<llbracket\>|<text|<samp|parse-sequence>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|currentSequence>>|\<rrbracket\>>>
  returns <math|<injr|<around*|(|x|)>>>.

  <subsubsection|<samp|current-is-Final>>

  \;

  <math|<rep|<text|<samp|'current-is-final'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|current-is-final>'>> :<1>\<vdash\><2>>

  \;

  Returns <math-tt|1><rsub|<2>> when <math|<around*|\<llbracket\>|<text|<samp|<math|currentSequence>>>|\<rrbracket\>>>
  returns <math|<around*|\<lfloor\>|2<rsup|32>-1|\<rfloor\>>>.

  <subsubsection|<samp|input-height-lock>>

  \;

  <math|<rep|<text|<samp|'input-height-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|input-height-lock>'>>
  :Index\<vdash\><maybe><around*|(|<maybe><around*|(|Height|)>|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  when <samp|input-is-final> returns <math|\<eta\><rsup|S><around*|(|<math-tt|1><rsub|<2>>|)>>
  and <math|<around*|\<llbracket\>|<text|<samp|parse-lock>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|lockTime>>|\<rrbracket\>>>
  returns <math|<injl|<around*|(|x|)>>>.

  Returns <math|\<emptyset\><rsup|<maybe>>> when the input index is out of
  range.

  <subsubsection|<samp|input-time-lock>>

  \;

  <math|<rep|<text|<samp|'input-time-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|input-time-lock>'>>
  :Index\<vdash\><maybe><around*|(|<maybe><around*|(|Time|)>|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  when <samp|input-is-final> returns <math|\<eta\><rsup|S><around*|(|<math-tt|1><rsub|<2>>|)>>
  and <math|<around*|\<llbracket\>|<text|<samp|parse-lock>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|lockTime>>|\<rrbracket\>>>
  returns <math|<injr|<around*|(|x|)>>>.

  Returns <math|\<emptyset\><rsup|<maybe>>> when the input index is out of
  range.

  <subsubsection|<samp|input-distance-lock>>

  \;

  <math|<rep|<text|<samp|'input-distance-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|input-distance-lock>'>>
  :Index\<vdash\><maybe><around*|(|<maybe><around*|(|Distance|)>|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  when <math|<maybe><around*|\<llbracket\>|<text|<samp|parse-sequence>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|inputSequence>>|\<rrbracket\>>>
  returns <math|\<eta\><rsup|S><around*|(|<injl|<around*|(|x|)>>|)>>.

  Returns <math|\<emptyset\><rsup|<maybe>>> when the input index is out of
  range.

  <subsubsection|<samp|input-duration-lock>>

  \;

  <math|<rep|<text|<samp|'input-duration-lock'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|input-duration-lock>'>>
  :Index\<vdash\><maybe><around*|(|<maybe><around*|(|Duration|)>|)>>

  \;

  Returns <math|\<eta\><rsup|S><around*|(|\<eta\><rsup|S><around*|(|x|)>|)>>
  when <math|<maybe><around*|\<llbracket\>|<text|<samp|parse-sequence>>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<text|<samp|inputSequence>>|\<rrbracket\>>>
  returns <math|\<eta\><rsup|S><around*|(|<injr|<around*|(|x|)>>|)>>.

  Returns <math|\<emptyset\><rsup|<maybe>>> when the input index is out of
  range.

  <subsubsection|<samp|input-is-final>>

  \;

  <math|<rep|<text|<samp|'input-is-final'>>|>\<assign\><verbatim|<around*|[|111|]>><rsub|<2>>\<cdummy\><rep|<value|subsection-nr>|>\<cdummy\><rep|<value|subsubsection-nr>|>>

  <math|<text|<samp|'<samp|input-is-final>'>>
  :Index\<vdash\><maybe><around*|(|<2>|)>>

  \;

  Returns \<eta\><rsup|S><around*|(|<math-tt|1><rsub|<2>>|)> when
  <math|<around*|\<llbracket\>|<text|<samp|<math|inputSequence>>>|\<rrbracket\>>>
  returns \<eta\><rsup|S><around*|(|<math|<around*|\<lfloor\>|2<rsup|32>-1|\<rfloor\>>>|)>.

  Returns <math|\<emptyset\><rsup|<maybe>>> when the input index is out of
  range.

  <subsection|Issuance>

  Notes: use <samp|IssuanceContractHash> and <samp|IssuanceEntropy> to decide
  which issuance kind, if any, is being invoked.

  <\itemize>
    <item><math|<samp|currentIssuance>\<of\><value|1>\<vdash\><maybe><around*|(|<2>|)>><with|color|red|Either
    a new issuance or reissuance or neither>

    <item><math|<samp|currentIssuanceAsset>\<of\><value|1>\<vdash\><maybe><around*|(|ExplicitAsset|)>>

    <item><math|<samp|currentIssuanceToken>\<of\><value|1>\<vdash\><maybe><around*|(|ExplicitAsset|)>>

    <item><math|<samp|inputIssuance>\<of\>Index\<vdash\><maybe><around*|(|<maybe><around*|(|<2>|)>|)>>

    <item><math|<samp|inputIssuanceAsset>\<of\>Index\<vdash\><maybe><around*|(|<maybe><around*|(|ExplicitAsset|)>|)>>

    <item><math|<samp|inputIssuanceToken>\<of\>Index\<vdash\><maybe><around*|(|<maybe><around*|(|ExplicitAsset|)>|)>>

    \;
  </itemize>

  <appendix|Alternative Serialization of Simplicity
  DAGs><label|app:AltSerialization>

  <with|color|red|DEPRICATED>

  This appendix presents an alternative, byte-oriented prefix code for
  Simplicity DAGs. This code is not as compact as the bit-oriented code
  presented in Section<nbsp><reference|ss:Serialization> and it imposes some
  arbitrary limits on the size of the DAG and witness values. Its only
  advantage is that it might be faster to decode. This code probably should
  not be used by any application and maybe should be removed from this
  report.

  First we define a byte-string serialization for numbers <math|i> known to
  be less than a bound <math|b> by determining the minimum number of bytes
  needed to fit a number less than <math|b>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|byteCode<around*|(|1,0|)>>|<cell|\<assign\>>|<cell|\<epsilon\><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|b,i|)>>|<cell|\<assign\>>|<cell|byteCode<around*|(|2<rsup|*8*n>,q|)>\<cdummy\>BE<around*|(|<around*|\<lfloor\>|i|\<rfloor\>><rsub|8>|)><htab|5mm>where
    2<rsup|8>*q\<leq\>i\<less\>2<rsup|8><around*|(|q+1|)> and
    2<rsup|8*n>\<less\>b\<leq\>2<rsup|8*<around*|(|n+1|)>> and i\<less\>b>>>>
  </eqnarray*>

  \;

  For witness data, which is a bit-string, we group the bits into bytes to
  form a byte-string, padding the least significant bits with zero bits.

  <\eqnarray*>
    <tformat|<table|<row|<cell|bytePad<around*|(|\<epsilon\>|)>>|<cell|\<assign\>>|<cell|\<epsilon\><rsub|<2><rsup|8>>>>|<row|<cell|bytePad<around*|(|b<rsub|0>\<blacktriangleleft\>b<rsub|1>\<blacktriangleleft\>b<rsub|2>\<blacktriangleleft\>b<rsub|3>\<blacktriangleleft\>b<rsub|4>\<blacktriangleleft\>b<rsub|5>\<blacktriangleleft\>b<rsub|6>\<blacktriangleleft\>b<rsub|7>\<blacktriangleleft\>v|)>>|<cell|\<assign\>>|<cell|<around*|\<langle\>|<around*|\<langle\>|<around*|\<langle\>|b<rsub|0>,b<rsub|1>|\<rangle\>>,<around*|\<langle\>|b<rsub|2>,b<rsub|3>|\<rangle\>>|\<rangle\>>,<around*|\<langle\>|<around*|\<langle\>|b<rsub|4>,b<rsub|5>|\<rangle\>>,<around*|\<langle\>|b<rsub|6>,b<rsub|7>|\<rangle\>>|\<rangle\>>|\<rangle\>>\<blacktriangleleft\>bytePad<around*|(|v|)>>>|<row|<cell|bytePad<around*|(|v|)>>|<cell|\<assign\>>|<cell|bytePad<around*|(|v\<cdummy\><verbatim|<around*|[|0|]>><rsup|8-<around*|\||v|\|>>|)><htab|5mm>when
    0\<less\><around*|\||v|\|>\<less\>8>>>>
  </eqnarray*>

  Note that by itself <math|bytePad> is not a prefix code and forgets how
  many bits where in the vector. Both issues are addressed by prefixing this
  encoding with the length of the number of bits in the original bit-string.

  Next we define a byte-string serialization for Node,
  <math|byteCode\<of\>\<bbb-N\>\<times\>Node\<rightarrow\><around*|(|<2><rsup|8>|)><rsup|\<ast\>>>.
  The first parameter to <math|byteCode>, <math|k>, is the index at which the
  Node occurs in the Dag. It is used to determine the bound on the size of
  the sub-expression offsets for serialization of those values.

  <\eqnarray*>
    <tformat|<table|<row|<cell|byteCode<around*|(|k,<text|<samp|`comp'>> 1
    1|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|00>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`case'>>
    1 1|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|01>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`pair'>>
    1 1|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|02>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`disconnect'>>
    1 1|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|03>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`comp'>>
    1 j|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|04>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,j-2|)><htab|5mm>where
    1\<less\>j>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`case'>> 1
    j|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|05>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,j-2|)><htab|5mm>where
    1\<less\>j>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`pair'>> 1
    j|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|06>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,j-2|)><htab|5mm>where
    1\<less\>j>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`disconnect'>> 1
    j|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|07>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,j-2|)><htab|5mm>where
    1\<less\>j>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`comp'>> i
    1|)>>|=|<cell|<verbatim|<around*|[|<math-tt|08>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,i-2|)><htab|5mm>where
    1\<less\>i>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`case'>> i
    1|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|09>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,i-2|)><htab|5mm>where
    1\<less\>i>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`pair'>> i
    1|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|0a>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,i-2|)><htab|5mm>where
    1\<less\>i>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`disconnect'>> i
    1|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|0b>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,i-2|)><htab|5mm>where
    1\<less\>i>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`comp'>> i
    j|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|0c>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,i-2|)>\<cdummy\>byteCode<around*|(|k-1,j-2|)><htab|5mm>where
    1\<less\>i and 1\<less\>j>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`case'>>
    i j|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|0d>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,i-2|)>\<cdummy\>byteCode<around*|(|k-1,j-2|)><htab|5mm>where
    1\<less\>i and 1\<less\>j>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`pair'>>
    i j|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|0e>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,i-2|)>\<cdummy\>byteCode<around*|(|k-1,j-2|)><htab|5mm>where
    1\<less\>i and 1\<less\>j>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`disconnect'>>
    i j|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|0f>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,i-2|)>\<cdummy\>byteCode<around*|(|k-1,j-2|)><htab|5mm>where
    1\<less\>i and 1\<less\>j>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`injl'>>
    1|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|10>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`injr'>>
    1|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|11>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`take'>>
    1|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|12>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`drop'>>
    1|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|13>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`injl'>>
    i|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|18>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,i-2|)><htab|5mm>where
    1\<less\>i>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`injr'>>
    i|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|19>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,i-2|)><htab|5mm>where
    1\<less\>i>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`take'>>
    i|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|1a>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,i-2|)><htab|5mm>where
    1\<less\>i>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`drop'>>
    i|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|1b>|]>><rsub|<2><rsup|8>>\<cdummy\>byteCode<around*|(|k-1,i-2|)><htab|5mm>where
    1\<less\>i>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`iden'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|20|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`unit'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|21|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`fail'>>
    b|)>>|<cell|=>|<cell|<verbatim|<around*|[|22|]>><rsub|<2><rsup|8>>\<cdummy\>BE<rsup|><around*|(|b|)>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`hidden'>>
    h|)>>|<cell|=>|<cell|<verbatim|<around*|[|23|]>><rsub|<2><rsup|8>>\<cdummy\>BE<rsup|><around*|(|h|)>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`witness'>>
    v|)>>|<cell|=>|<cell|BE<around*|(|<around*|\<lfloor\>|<math-tt|80><rsub|<2><rsup|8>>+<around*|\||v|\|>|\<rfloor\>><rsub|8>|)>\<cdummy\>bytePad<around*|(|v|)><htab|5mm>where
    <around*|\||v|\|>\<less\>127>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`witness'>>
    v|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|ff>|]>><rsub|<2><rsup|8>>\<cdummy\>BE<around*|(|<around*|\<lfloor\>|<around*|\||v|\|>|\<rfloor\>><rsub|16>|)><rsub|>\<cdummy\>bytePad<around*|(|v|)><htab|5mm>where
    127 \<leq\><around*|\||v|\|>\<less\>2<rsup|16>>>>>
  </eqnarray*>

  The byte codes for primitives begin with a byte between
  <math|<verbatim|[24]><rsub|<2><rsup|8>>> and
  <math|<verbatim|[<math-tt|3f>]><rsub|<2><rsup|8>>> inclusive. The codes can
  contain multiple bytes. However, for the Bitcoin primitives, we only need
  to use one byte per primitive.

  <\eqnarray*>
    <tformat|<table|<row|<cell|byteCode<around*|(|k,<text|<samp|`version'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|24>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`lockTime'>>|)>>|<cell|=>|<cell|<verbatim|<verbatim|<around*|[|<math-tt|25>|]>>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`inputsHash'>>|)>>|<cell|=>|<cell|<verbatim|<verbatim|<around*|[|<math-tt|26>|]>>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`outputsHash'>>|)>>|<cell|=>|<cell|<verbatim|<verbatim|<around*|[|<math-tt|27>|]>>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`numInputs'>>|)>>|<cell|=>|<verbatim|<verbatim|<around*|[|<math-tt|28>|]>>><rsub|<2><rsup|8>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`totalnputValue'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|29>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`currentPrevOutpoint'>>|)>>|<cell|=>|<cell|<verbatim|<verbatim|<around*|[|<math-tt|2a>|]>>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`currentValue'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|2b>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`currentSequence'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|2c>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`currentIndex'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|2d>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`inputPrevOutpoint'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|2e>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`inputValue'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|2f>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`inputSequence'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|30>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`numOutputs'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|31>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`totalOutputValue'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|32>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`outputValue'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|33>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`outputScriptHash'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|34>|]>><rsub|<2><rsup|8>>>>|<row|<cell|byteCode<around*|(|k,<text|<samp|`scriptCMR'>>|)>>|<cell|=>|<cell|<verbatim|<around*|[|<math-tt|35>|]>><rsub|<2><rsup|8>>>>>>
  </eqnarray*>

  We define a byte-string prefix code for Simplicity DAGs as a concatenation
  of byte-string codes of its nodes, terminated by a sentinel value that has
  been reserved as an end-of-stream byte.

  <\equation*>
    byteCode<around*|(|l|)>\<assign\><around*|(|<around*|(|\<mu\><rsup|\<ast\>>\<circ\>\<eta\><rsup|<maybe>>\<circ\>byteCode<rsup|+>\<circ\>indexed|)><around*|(|l|)>|)>\<cdummy\><verbatim|<around*|[|<math-tt|1f>|]>><rsub|<2><rsup|8>>
  </equation*>

  Notice that while <math|byteCode<around*|(|0,x|)>> for <math|x\<of\>Node>
  seems like it could call <math|byteCode<around*|(|-1,n|)>> for some
  <math|n:\<bbb-N\>>, this can never happen for Simplicity DAGs. Recall from
  Section<nbsp><reference|ss:DAGs>, that a well-formed Simplicity DAG,
  <math|l\<of\>Node<rsup|+>>, satisfies the condition

  <\equation*>
    \<forall\><around*|\<langle\>|i,a|\<rangle\>>\<in\>indexed<around*|(|l|)>\<point\>\<forall\>j\<in\>ref<around*|(|a|)>\<point\>0\<less\>j\<leq\>i<text|.>
  </equation*>

  The condition on DAGs implies that <math|<around*|\||ref<around*|(|l<around*|[|0|]>|)>|\|>=0>.
  This condition means that <math|byteCode<around*|(|-1,n|)>> never occurs
  for any <math|n:\<bbb-N\>>.

  <\bibliography|bib|tm-plain|Simplicity.bib>
    <\bib-list|18>
      <bibitem*|1><label|bib-Appel:2015>A. W.<nbsp>Appel.<newblock>
      Verification of a cryptographic primitive: SHA-256.<newblock>
      <with|font-shape|italic|ACM Trans. Program. Lang. Syst.>, 37(2):7--1,
      apr 2015.<newblock>

      <bibitem*|2><label|bib-script>Bitcoinwiki.<newblock> Script.<newblock>
      <slink|https://en.bitcoin.it/w/index.php?title=Scriptoldid=61707>,
      2016.<newblock>

      <bibitem*|3><label|bib-Carette:2009>J.<nbsp>Carette,
      O.<nbsp>Kiselyov<localize| and >C.<nbsp>Shan.<newblock> Finally
      tagless, partially evaluated: tagless staged interpreters for simpler
      typed languages.<newblock> <with|font-shape|italic|J. Funct. Program.>,
      19(5):509--543, sep 2009.<newblock>

      <bibitem*|4><label|bib-sec2>Certicom Research.<newblock> Standards for
      Efficient Cryptography 2: Recommended Elliptic Curve Domain
      Parameters.<newblock> Standard SEC2, Certicom Corp., Mississauga, ON,
      USA, Sep 2000.<newblock>

      <bibitem*|5><label|bib-Coq:manual>The<nbsp>Coq Development
      Team.<newblock> <with|font-shape|italic|The Coq Proof Assistant
      Reference Manual, version 8.7>.<newblock> Oct 2017.<newblock>

      <bibitem*|6><label|bib-garillot:2009>F.<nbsp>Garillot,
      G.<nbsp>Gonthier, A.<nbsp>Mahboubi<localize| and
      >L.<nbsp>Rideau.<newblock> Packaging Mathematical Structures.<newblock>
      <localize|In >Tobias<nbsp>Nipkow<localize| and
      >Christian<nbsp>Urban<localize|, editors>,
      <with|font-shape|italic|Theorem Proving in Higher Order Logics>,
      <localize|volume> 5674<localize| of ><with|font-shape|italic|Lecture
      Notes in Computer Science>. Munich, Germany, 2009. Springer.<newblock>

      <bibitem*|7><label|bib-gentzen>G.<nbsp>Gentzen.<newblock>
      Investigations into logical deduction.<newblock> <localize|In
      >M.E.<nbsp>Szabo<localize|, editor>, <with|font-shape|italic|The
      collected papers of Gerhard Gentzen>, Studies in logic and the
      foundations of mathematics, <localize|chapter> 3. \ North-Holland Pub.
      Co., 1969.<newblock>

      <bibitem*|8><label|bib-King1993>D. J.<nbsp>King<localize| and
      >P.<nbsp>Wadler.<newblock> <with|font-shape|italic|Combining Monads>,
      <localize|pages >134--143.<newblock> Springer London, London,
      1993.<newblock>

      <bibitem*|9><label|bib-Mahboubi:2013>A.<nbsp>Mahboubi<localize| and
      >E.<nbsp>Tassi.<newblock> Canonical structures for the working Coq
      user.<newblock> <localize|In ><with|font-shape|italic|Proceedings of
      the 4th International Conference on Interactive Theorem Proving>,
      ITP'13, <localize|pages >19--34. Berlin, Heidelberg, 2013.
      Springer-Verlag.<newblock>

      <bibitem*|10><label|bib-Mairson:1989>H. G.<nbsp>Mairson.<newblock>
      Deciding ML typability is complete for deterministic exponential
      time.<newblock> <localize|In ><with|font-shape|italic|Proceedings of
      the 17th ACM SIGPLAN-SIGACT Symposium on Principles of Programming
      Languages>, POPL '90, <localize|pages >382--401. New York, NY, USA,
      1990. ACM.<newblock>

      <bibitem*|11><label|bib-bitcoin>S.<nbsp>Nakamoto.<newblock> Bitcoin: A
      peer-to-peer electronic cash system.<newblock>
      <slink|http://bitcoin.org/bitcoin.pdf>, Nov 2008.<newblock>

      <bibitem*|12><label|bib-satoshiScript>S.<nbsp>Nakamoto.<newblock> Re:
      Transactions and Scripts: DUP HASH160 ... EQUALVERIFY
      CHECKSIG.<newblock> <slink|https://bitcointalk.org/index.php?topic=195.msg1611#msg1611>,
      Jun 2010.<newblock>

      <bibitem*|13><label|bib-sha>National institute of standards and
      technology.<newblock> FIPS 180-4, secure hash standard, federal
      information processing standard (FIPS), publication 180-4.<newblock>
      <localize|Technical Report>, DEPARTMENT OF COMMERCE, aug
      2015.<newblock>

      <bibitem*|14><label|bib-oconnor2014>R.<nbsp>O'Connor.<newblock> Van
      Laarhoven free monad.<newblock> Feb 2014.<newblock> Blog post,
      <slink|http://r6.ca/blog/20140210T181244Z.html>.<newblock>

      <bibitem*|15><label|bib-unification>M. S.<nbsp>Paterson<localize| and
      >M. N.<nbsp>Wegman.<newblock> Linear unification.<newblock>
      <with|font-shape|italic|Journal of Computer and System Sciences>,
      16(2):158--167, 1978.<newblock>

      <bibitem*|16><label|bib-f-algebra>Wikipedia contributors.<newblock>
      F-algebra <emdash> Wikipedia, the free encyclopedia.<newblock>
      <slink|https://en.wikipedia.org/w/index.php?title=F-algebraoldid=814231684>,
      2017.<newblock>

      <bibitem*|17><label|bib-libsecp256k1>P.<nbsp>Wuille.<newblock>
      Libsecp256k1.<newblock> <slink|https://github.com/bitcoin-core/secp256k1/tree/1e6f1f5ad5e7f1e3ef79313ec02023902bf8175c>,
      May 2018.<newblock>

      <bibitem*|18><label|bib-bip-0340>P.<nbsp>Wuille, J.<nbsp>Nick<localize|
      and >T.<nbsp>Ruffing.<newblock> Bip-0340.<newblock> 2020.<newblock>
      <slink|Https://github.com/bitcoin/bips/blob/master/bip-0340.mediawiki>.<newblock>
    </bib-list>
  </bibliography>
</body>

<\initial>
  <\collection>
    <associate|page-medium|papyrus>
    <associate|page-type|letter>
    <associate|par-mode|justify>
    <associate|preamble|false>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|SS:Coq:MerkleRoots|<tuple|8.5|?>>
    <associate|app:AltSerialization|<tuple|C|?>>
    <associate|app:ElementsTransactions|<tuple|A|?>>
    <associate|auto-1|<tuple|1|?>>
    <associate|auto-10|<tuple|2.2|?>>
    <associate|auto-100|<tuple|7.1|?>>
    <associate|auto-101|<tuple|7.1.1|?>>
    <associate|auto-102|<tuple|7.1.2|?>>
    <associate|auto-103|<tuple|7.1.2.1|?>>
    <associate|auto-104|<tuple|7.1.2.2|?>>
    <associate|auto-105|<tuple|7.2|?>>
    <associate|auto-106|<tuple|7.2.1|?>>
    <associate|auto-107|<tuple|7.2.2|?>>
    <associate|auto-108|<tuple|7.2.3|?>>
    <associate|auto-109|<tuple|8|?>>
    <associate|auto-11|<tuple|2.2.1|?>>
    <associate|auto-110|<tuple|8.1|?>>
    <associate|auto-111|<tuple|8.2|?>>
    <associate|auto-112|<tuple|8.2.1|?>>
    <associate|auto-113|<tuple|8.2.2|?>>
    <associate|auto-114|<tuple|8.2.2.1|?>>
    <associate|auto-115|<tuple|8.2.2.2|?>>
    <associate|auto-116|<tuple|8.2.2.3|?>>
    <associate|auto-117|<tuple|8.2.3|?>>
    <associate|auto-118|<tuple|8.3|?>>
    <associate|auto-119|<tuple|8.3.1|?>>
    <associate|auto-12|<tuple|2.2.2|?>>
    <associate|auto-120|<tuple|8.3.2|?>>
    <associate|auto-121|<tuple|8.3.3|?>>
    <associate|auto-122|<tuple|8.4|?>>
    <associate|auto-123|<tuple|8.1|?>>
    <associate|auto-124|<tuple|8.4.1|?>>
    <associate|auto-125|<tuple|8.4.2|?>>
    <associate|auto-126|<tuple|8.4.3|?>>
    <associate|auto-127|<tuple|8.4.4|?>>
    <associate|auto-128|<tuple|8.4.4.1|?>>
    <associate|auto-129|<tuple|8.4.5|?>>
    <associate|auto-13|<tuple|2.3|?>>
    <associate|auto-130|<tuple|8.4.6|?>>
    <associate|auto-131|<tuple|8.5|?>>
    <associate|auto-132|<tuple|8.6|?>>
    <associate|auto-133|<tuple|8.6.1|?>>
    <associate|auto-134|<tuple|8.6.1.1|?>>
    <associate|auto-135|<tuple|8.6.2|?>>
    <associate|auto-136|<tuple|8.6.3|?>>
    <associate|auto-137|<tuple|9|?>>
    <associate|auto-138|<tuple|9.1|?>>
    <associate|auto-139|<tuple|9.1.1|?>>
    <associate|auto-14|<tuple|2.3.1|?>>
    <associate|auto-140|<tuple|9.1.2|?>>
    <associate|auto-141|<tuple|9.1.3|?>>
    <associate|auto-142|<tuple|9.1.4|?>>
    <associate|auto-143|<tuple|9.1.5|?>>
    <associate|auto-144|<tuple|9.1.5.1|?>>
    <associate|auto-145|<tuple|9.1.5.2|?>>
    <associate|auto-146|<tuple|9.1.5.3|?>>
    <associate|auto-147|<tuple|9.1.5.4|?>>
    <associate|auto-148|<tuple|9.1.5.5|?>>
    <associate|auto-149|<tuple|9.1.6|?>>
    <associate|auto-15|<tuple|2.3.2|?>>
    <associate|auto-150|<tuple|9.1.6.1|?>>
    <associate|auto-151|<tuple|9.1.6.2|?>>
    <associate|auto-152|<tuple|9.1.6.3|?>>
    <associate|auto-153|<tuple|9.1.7|?>>
    <associate|auto-154|<tuple|9.1.7.1|?>>
    <associate|auto-155|<tuple|9.1.7.2|?>>
    <associate|auto-156|<tuple|9.1.7.3|?>>
    <associate|auto-157|<tuple|9.2|?>>
    <associate|auto-158|<tuple|9.2.1|?>>
    <associate|auto-159|<tuple|9.2.2|?>>
    <associate|auto-16|<tuple|2.3.3|?>>
    <associate|auto-160|<tuple|9.2.3|?>>
    <associate|auto-161|<tuple|9.2.4|?>>
    <associate|auto-162|<tuple|9.2.5|?>>
    <associate|auto-163|<tuple|9.2.6|?>>
    <associate|auto-164|<tuple|9.2.6.1|?>>
    <associate|auto-165|<tuple|9.2.6.2|?>>
    <associate|auto-166|<tuple|9.2.7|?>>
    <associate|auto-167|<tuple|9.3|?>>
    <associate|auto-168|<tuple|9.4|?>>
    <associate|auto-169|<tuple|9.4.1|?>>
    <associate|auto-17|<tuple|2.3.4|?>>
    <associate|auto-170|<tuple|9.4.2|?>>
    <associate|auto-171|<tuple|9.5|?>>
    <associate|auto-172|<tuple|10|?>>
    <associate|auto-173|<tuple|A|?>>
    <associate|auto-174|<tuple|A.1|?>>
    <associate|auto-175|<tuple|A.1.1|?>>
    <associate|auto-176|<tuple|A.1.2|?>>
    <associate|auto-177|<tuple|A.1.3|?>>
    <associate|auto-178|<tuple|B|?>>
    <associate|auto-179|<tuple|B.1|?>>
    <associate|auto-18|<tuple|2.3.4.1|?>>
    <associate|auto-180|<tuple|B.1.1|?>>
    <associate|auto-181|<tuple|B.1.1.1|?>>
    <associate|auto-182|<tuple|B.1.1.2|?>>
    <associate|auto-183|<tuple|B.1.1.3|?>>
    <associate|auto-184|<tuple|B.1.1.4|?>>
    <associate|auto-185|<tuple|B.1.1.5|?>>
    <associate|auto-186|<tuple|B.1.1.6|?>>
    <associate|auto-187|<tuple|B.1.1.7|?>>
    <associate|auto-188|<tuple|B.1.1.8|?>>
    <associate|auto-189|<tuple|B.1.1.9|?>>
    <associate|auto-19|<tuple|2.4|?>>
    <associate|auto-190|<tuple|B.1.1.10|?>>
    <associate|auto-191|<tuple|B.1.1.11|?>>
    <associate|auto-192|<tuple|B.1.1.12|?>>
    <associate|auto-193|<tuple|B.1.1.13|?>>
    <associate|auto-194|<tuple|B.1.1.14|?>>
    <associate|auto-195|<tuple|B.1.1.15|?>>
    <associate|auto-196|<tuple|B.1.1.16|?>>
    <associate|auto-197|<tuple|B.1.1.17|?>>
    <associate|auto-198|<tuple|B.1.1.18|?>>
    <associate|auto-199|<tuple|B.1.1.19|?>>
    <associate|auto-2|<tuple|1.1|?>>
    <associate|auto-20|<tuple|2.4.1|?>>
    <associate|auto-200|<tuple|B.1.1.20|?>>
    <associate|auto-201|<tuple|B.1.1.21|?>>
    <associate|auto-202|<tuple|B.1.1.22|?>>
    <associate|auto-203|<tuple|B.1.1.23|?>>
    <associate|auto-204|<tuple|B.1.1.24|?>>
    <associate|auto-205|<tuple|B.1.1.25|?>>
    <associate|auto-206|<tuple|B.1.1.26|?>>
    <associate|auto-207|<tuple|B.1.1.27|?>>
    <associate|auto-208|<tuple|B.1.1.28|?>>
    <associate|auto-209|<tuple|B.1.1.29|?>>
    <associate|auto-21|<tuple|2.4.2|?>>
    <associate|auto-210|<tuple|B.1.2|?>>
    <associate|auto-211|<tuple|B.1.2.1|?>>
    <associate|auto-212|<tuple|B.1.2.2|?>>
    <associate|auto-213|<tuple|B.1.2.3|?>>
    <associate|auto-214|<tuple|B.1.2.4|?>>
    <associate|auto-215|<tuple|B.1.2.5|?>>
    <associate|auto-216|<tuple|B.1.2.6|?>>
    <associate|auto-217|<tuple|B.1.2.7|?>>
    <associate|auto-218|<tuple|B.1.2.8|?>>
    <associate|auto-219|<tuple|B.1.2.9|?>>
    <associate|auto-22|<tuple|3|?>>
    <associate|auto-220|<tuple|B.1.2.10|?>>
    <associate|auto-221|<tuple|B.1.2.11|?>>
    <associate|auto-222|<tuple|B.1.2.12|?>>
    <associate|auto-223|<tuple|B.1.2.13|?>>
    <associate|auto-224|<tuple|B.1.2.14|?>>
    <associate|auto-225|<tuple|B.1.2.15|?>>
    <associate|auto-226|<tuple|B.1.2.16|?>>
    <associate|auto-227|<tuple|B.1.2.17|?>>
    <associate|auto-228|<tuple|B.1.2.18|?>>
    <associate|auto-229|<tuple|B.1.2.19|?>>
    <associate|auto-23|<tuple|3.1|?>>
    <associate|auto-230|<tuple|B.1.2.20|?>>
    <associate|auto-231|<tuple|B.1.2.21|?>>
    <associate|auto-232|<tuple|B.1.2.22|?>>
    <associate|auto-233|<tuple|B.1.2.23|?>>
    <associate|auto-234|<tuple|B.1.2.24|?>>
    <associate|auto-235|<tuple|B.1.2.25|?>>
    <associate|auto-236|<tuple|B.1.2.26|?>>
    <associate|auto-237|<tuple|B.1.2.27|?>>
    <associate|auto-238|<tuple|B.1.2.28|?>>
    <associate|auto-239|<tuple|B.1.2.29|?>>
    <associate|auto-24|<tuple|3.1.1|?>>
    <associate|auto-240|<tuple|B.1.2.30|?>>
    <associate|auto-241|<tuple|B.1.2.31|?>>
    <associate|auto-242|<tuple|B.1.2.32|?>>
    <associate|auto-243|<tuple|B.1.2.33|?>>
    <associate|auto-244|<tuple|B.1.2.34|?>>
    <associate|auto-245|<tuple|B.1.2.35|?>>
    <associate|auto-246|<tuple|B.1.2.36|?>>
    <associate|auto-247|<tuple|B.1.2.37|?>>
    <associate|auto-248|<tuple|B.1.2.38|?>>
    <associate|auto-249|<tuple|B.1.2.39|?>>
    <associate|auto-25|<tuple|3.1.2|?>>
    <associate|auto-250|<tuple|B.1.2.40|?>>
    <associate|auto-251|<tuple|B.1.2.41|?>>
    <associate|auto-252|<tuple|B.1.2.42|?>>
    <associate|auto-253|<tuple|B.1.2.43|?>>
    <associate|auto-254|<tuple|B.1.3|?>>
    <associate|auto-255|<tuple|B.1.3.1|?>>
    <associate|auto-256|<tuple|B.1.3.1.1|?>>
    <associate|auto-257|<tuple|B.1.3.1.2|?>>
    <associate|auto-258|<tuple|B.1.3.2|?>>
    <associate|auto-259|<tuple|B.1.3.2.1|?>>
    <associate|auto-26|<tuple|3.1.3|?>>
    <associate|auto-260|<tuple|B.1.3.2.2|?>>
    <associate|auto-261|<tuple|B.1.3.2.3|?>>
    <associate|auto-262|<tuple|B.1.3.2.4|?>>
    <associate|auto-263|<tuple|B.1.3.2.5|?>>
    <associate|auto-264|<tuple|B.1.3.2.6|?>>
    <associate|auto-265|<tuple|B.1.3.3|?>>
    <associate|auto-266|<tuple|B.1.3.4|?>>
    <associate|auto-267|<tuple|B.1.4|?>>
    <associate|auto-268|<tuple|B.1.4.1|?>>
    <associate|auto-269|<tuple|B.1.4.1.1|?>>
    <associate|auto-27|<tuple|3.2|?>>
    <associate|auto-270|<tuple|B.1.4.1.2|?>>
    <associate|auto-271|<tuple|B.1.4.1.3|?>>
    <associate|auto-272|<tuple|B.1.4.1.4|?>>
    <associate|auto-273|<tuple|B.1.4.1.5|?>>
    <associate|auto-274|<tuple|B.1.4.1.6|?>>
    <associate|auto-275|<tuple|B.1.4.1.7|?>>
    <associate|auto-276|<tuple|B.1.4.1.8|?>>
    <associate|auto-277|<tuple|B.1.4.1.9|?>>
    <associate|auto-278|<tuple|B.1.4.1.10|?>>
    <associate|auto-279|<tuple|B.1.4.1.11|?>>
    <associate|auto-28|<tuple|3.2.1|?>>
    <associate|auto-280|<tuple|B.1.4.1.12|?>>
    <associate|auto-281|<tuple|B.1.4.1.13|?>>
    <associate|auto-282|<tuple|B.1.4.1.14|?>>
    <associate|auto-283|<tuple|B.1.4.1.15|?>>
    <associate|auto-284|<tuple|B.1.4.1.16|?>>
    <associate|auto-285|<tuple|B.1.4.1.17|?>>
    <associate|auto-286|<tuple|B.1.4.1.18|?>>
    <associate|auto-287|<tuple|B.1.4.1.19|?>>
    <associate|auto-288|<tuple|B.1.4.1.20|?>>
    <associate|auto-289|<tuple|B.1.4.1.21|?>>
    <associate|auto-29|<tuple|3.2.2|?>>
    <associate|auto-290|<tuple|B.1.4.1.22|?>>
    <associate|auto-291|<tuple|B.1.4.1.23|?>>
    <associate|auto-292|<tuple|B.1.4.1.24|?>>
    <associate|auto-293|<tuple|B.1.4.1.25|?>>
    <associate|auto-294|<tuple|B.1.4.1.26|?>>
    <associate|auto-295|<tuple|B.1.4.1.27|?>>
    <associate|auto-296|<tuple|B.1.4.1.28|?>>
    <associate|auto-297|<tuple|B.1.4.1.29|?>>
    <associate|auto-298|<tuple|B.1.4.1.30|?>>
    <associate|auto-299|<tuple|B.1.4.1.31|?>>
    <associate|auto-3|<tuple|1.2|?>>
    <associate|auto-30|<tuple|3.2.3|?>>
    <associate|auto-300|<tuple|B.1.4.1.32|?>>
    <associate|auto-301|<tuple|B.1.4.1.33|?>>
    <associate|auto-302|<tuple|B.1.4.1.34|?>>
    <associate|auto-303|<tuple|B.1.4.1.35|?>>
    <associate|auto-304|<tuple|B.1.4.1.36|?>>
    <associate|auto-305|<tuple|B.1.4.1.37|?>>
    <associate|auto-306|<tuple|B.1.4.1.38|?>>
    <associate|auto-307|<tuple|B.1.4.1.39|?>>
    <associate|auto-308|<tuple|B.1.4.1.40|?>>
    <associate|auto-309|<tuple|B.1.4.1.41|?>>
    <associate|auto-31|<tuple|3.2.4|?>>
    <associate|auto-310|<tuple|B.1.4.1.42|?>>
    <associate|auto-311|<tuple|B.1.4.1.43|?>>
    <associate|auto-312|<tuple|B.1.4.1.44|?>>
    <associate|auto-313|<tuple|B.1.4.1.45|?>>
    <associate|auto-314|<tuple|B.1.5|?>>
    <associate|auto-315|<tuple|B.1.5.1|?>>
    <associate|auto-316|<tuple|B.1.5.1.1|?>>
    <associate|auto-317|<tuple|B.1.5.1.2|?>>
    <associate|auto-318|<tuple|B.1.5.1.3|?>>
    <associate|auto-319|<tuple|B.1.5.1.4|?>>
    <associate|auto-32|<tuple|3.2.5|?>>
    <associate|auto-320|<tuple|B.1.5.1.5|?>>
    <associate|auto-321|<tuple|B.1.5.1.6|?>>
    <associate|auto-322|<tuple|B.1.5.1.7|?>>
    <associate|auto-323|<tuple|B.1.6|?>>
    <associate|auto-324|<tuple|B.1.6.1|?>>
    <associate|auto-325|<tuple|B.1.6.1.1|?>>
    <associate|auto-326|<tuple|B.1.6.1.2|?>>
    <associate|auto-327|<tuple|B.1.6.1.3|?>>
    <associate|auto-328|<tuple|B.1.6.1.4|?>>
    <associate|auto-329|<tuple|B.1.6.1.5|?>>
    <associate|auto-33|<tuple|3.2.6|?>>
    <associate|auto-330|<tuple|B.1.6.1.6|?>>
    <associate|auto-331|<tuple|B.1.6.1.7|?>>
    <associate|auto-332|<tuple|B.1.6.1.8|?>>
    <associate|auto-333|<tuple|B.1.6.1.9|?>>
    <associate|auto-334|<tuple|B.1.6.1.10|?>>
    <associate|auto-335|<tuple|B.1.6.1.11|?>>
    <associate|auto-336|<tuple|B.1.6.1.12|?>>
    <associate|auto-337|<tuple|B.1.6.1.13|?>>
    <associate|auto-338|<tuple|B.1.6.1.14|?>>
    <associate|auto-339|<tuple|B.1.7|?>>
    <associate|auto-34|<tuple|3.2.7|?>>
    <associate|auto-340|<tuple|B.1.7.1|?>>
    <associate|auto-341|<tuple|B.1.7.2|?>>
    <associate|auto-342|<tuple|B.1.8|?>>
    <associate|auto-343|<tuple|B.1.8.1|?>>
    <associate|auto-344|<tuple|B.1.8.2|?>>
    <associate|auto-345|<tuple|B.1.8.3|?>>
    <associate|auto-346|<tuple|B.2|?>>
    <associate|auto-347|<tuple|B.2.1|?>>
    <associate|auto-348|<tuple|B.2.2|?>>
    <associate|auto-349|<tuple|B.2.3|?>>
    <associate|auto-35|<tuple|3.2.8|?>>
    <associate|auto-350|<tuple|B.2.3.1|?>>
    <associate|auto-351|<tuple|B.2.3.2|?>>
    <associate|auto-352|<tuple|B.2.3.3|?>>
    <associate|auto-353|<tuple|B.2.3.4|?>>
    <associate|auto-354|<tuple|B.2.3.5|?>>
    <associate|auto-355|<tuple|B.2.3.6|?>>
    <associate|auto-356|<tuple|B.2.3.7|?>>
    <associate|auto-357|<tuple|B.2.3.8|?>>
    <associate|auto-358|<tuple|B.2.3.9|?>>
    <associate|auto-359|<tuple|B.2.3.10|?>>
    <associate|auto-36|<tuple|3.2.9|?>>
    <associate|auto-360|<tuple|B.2.3.11|?>>
    <associate|auto-361|<tuple|B.2.3.12|?>>
    <associate|auto-362|<tuple|B.2.3.13|?>>
    <associate|auto-363|<tuple|B.2.3.14|?>>
    <associate|auto-364|<tuple|B.2.3.15|?>>
    <associate|auto-365|<tuple|B.3|?>>
    <associate|auto-366|<tuple|B.3.1|?>>
    <associate|auto-367|<tuple|B.3.2|?>>
    <associate|auto-368|<tuple|B.3.2.1|?>>
    <associate|auto-369|<tuple|B.3.2.2|?>>
    <associate|auto-37|<tuple|3.2.10|?>>
    <associate|auto-370|<tuple|B.3.2.3|?>>
    <associate|auto-371|<tuple|B.3.2.4|?>>
    <associate|auto-372|<tuple|B.3.2.5|?>>
    <associate|auto-373|<tuple|B.3.2.6|?>>
    <associate|auto-374|<tuple|B.3.2.7|?>>
    <associate|auto-375|<tuple|B.3.2.8|?>>
    <associate|auto-376|<tuple|B.3.2.9|?>>
    <associate|auto-377|<tuple|B.3.2.10|?>>
    <associate|auto-378|<tuple|B.3.2.11|?>>
    <associate|auto-379|<tuple|B.3.2.12|?>>
    <associate|auto-38|<tuple|3.2.11|?>>
    <associate|auto-380|<tuple|B.3.2.13|?>>
    <associate|auto-381|<tuple|B.3.2.14|?>>
    <associate|auto-382|<tuple|B.3.2.15|?>>
    <associate|auto-383|<tuple|B.3.3|?>>
    <associate|auto-384|<tuple|C|?>>
    <associate|auto-385|<tuple|C|?>>
    <associate|auto-39|<tuple|3.3|?>>
    <associate|auto-4|<tuple|1.2.1|?>>
    <associate|auto-40|<tuple|3.3.1|?>>
    <associate|auto-41|<tuple|3.3.2|?>>
    <associate|auto-42|<tuple|3.3.3|?>>
    <associate|auto-43|<tuple|3.3.4|?>>
    <associate|auto-44|<tuple|3.3.5|?>>
    <associate|auto-45|<tuple|3.3.6|?>>
    <associate|auto-46|<tuple|3.3.6.1|?>>
    <associate|auto-47|<tuple|3.3.7|?>>
    <associate|auto-48|<tuple|3.3.7.1|?>>
    <associate|auto-49|<tuple|3.3.7.2|?>>
    <associate|auto-5|<tuple|1.2.2|?>>
    <associate|auto-50|<tuple|3.3.7.3|?>>
    <associate|auto-51|<tuple|3.4|?>>
    <associate|auto-52|<tuple|3.5|?>>
    <associate|auto-53|<tuple|3.5.1|?>>
    <associate|auto-54|<tuple|3.5.2|?>>
    <associate|auto-55|<tuple|3.1|?>>
    <associate|auto-56|<tuple|3.5.2.1|?>>
    <associate|auto-57|<tuple|3.5.2.2|?>>
    <associate|auto-58|<tuple|3.5.2.3|?>>
    <associate|auto-59|<tuple|3.5.2.4|?>>
    <associate|auto-6|<tuple|1.2.3|?>>
    <associate|auto-60|<tuple|3.5.2.5|?>>
    <associate|auto-61|<tuple|3.5.2.6|?>>
    <associate|auto-62|<tuple|3.5.3|?>>
    <associate|auto-63|<tuple|3.5.3.1|?>>
    <associate|auto-64|<tuple|3.6|?>>
    <associate|auto-65|<tuple|3.6.1|?>>
    <associate|auto-66|<tuple|3.6.1.1|?>>
    <associate|auto-67|<tuple|3.6.1.2|?>>
    <associate|auto-68|<tuple|3.6.2|?>>
    <associate|auto-69|<tuple|3.7|?>>
    <associate|auto-7|<tuple|2|?>>
    <associate|auto-70|<tuple|3.8|?>>
    <associate|auto-71|<tuple|4|?>>
    <associate|auto-72|<tuple|4.1|?>>
    <associate|auto-73|<tuple|4.2|?>>
    <associate|auto-74|<tuple|4.2.1|?>>
    <associate|auto-75|<tuple|4.2.2|?>>
    <associate|auto-76|<tuple|4.3|?>>
    <associate|auto-77|<tuple|4.3.1|?>>
    <associate|auto-78|<tuple|4.3.2|?>>
    <associate|auto-79|<tuple|4.3.2.1|?>>
    <associate|auto-8|<tuple|2.1|?>>
    <associate|auto-80|<tuple|4.3.2.2|?>>
    <associate|auto-81|<tuple|4.4|?>>
    <associate|auto-82|<tuple|4.4.1|?>>
    <associate|auto-83|<tuple|4.4.1.1|?>>
    <associate|auto-84|<tuple|4.4.1.2|?>>
    <associate|auto-85|<tuple|4.5|?>>
    <associate|auto-86|<tuple|4.5.1|?>>
    <associate|auto-87|<tuple|4.6|?>>
    <associate|auto-88|<tuple|4.7|?>>
    <associate|auto-89|<tuple|4.7.1|?>>
    <associate|auto-9|<tuple|2.1.1|?>>
    <associate|auto-90|<tuple|5|?>>
    <associate|auto-91|<tuple|6|?>>
    <associate|auto-92|<tuple|6.1|?>>
    <associate|auto-93|<tuple|6.1.1|?>>
    <associate|auto-94|<tuple|6.1.1.1|?>>
    <associate|auto-95|<tuple|6.2|?>>
    <associate|auto-96|<tuple|6.2.1|?>>
    <associate|auto-97|<tuple|6.3|?>>
    <associate|auto-98|<tuple|6.3.1|?>>
    <associate|auto-99|<tuple|7|?>>
    <associate|bib-Appel:2015|<tuple|1|?>>
    <associate|bib-Carette:2009|<tuple|3|?>>
    <associate|bib-Coq:manual|<tuple|5|?>>
    <associate|bib-King1993|<tuple|8|?>>
    <associate|bib-Mahboubi:2013|<tuple|9|?>>
    <associate|bib-Mairson:1989|<tuple|10|?>>
    <associate|bib-bip-0340|<tuple|18|?>>
    <associate|bib-bitcoin|<tuple|11|?>>
    <associate|bib-f-algebra|<tuple|16|?>>
    <associate|bib-garillot:2009|<tuple|6|?>>
    <associate|bib-gentzen|<tuple|7|?>>
    <associate|bib-libsecp256k1|<tuple|17|?>>
    <associate|bib-oconnor2014|<tuple|14|?>>
    <associate|bib-satoshiScript|<tuple|12|?>>
    <associate|bib-script|<tuple|2|?>>
    <associate|bib-sec2|<tuple|4|?>>
    <associate|bib-sha|<tuple|13|?>>
    <associate|bib-unification|<tuple|15|?>>
    <associate|chapter:preliminaries|<tuple|2|?>>
    <associate|fig:inheritance|<tuple|8.1|?>>
    <associate|footnote-2.1|<tuple|2.1|?>>
    <associate|footnote-3.1|<tuple|3.1|?>>
    <associate|footnote-3.2|<tuple|3.2|?>>
    <associate|footnr-2.1|<tuple|2.1|?>>
    <associate|footnr-3.1|<tuple|3.1|?>>
    <associate|footnr-3.2|<tuple|3.2|?>>
    <associate|full-adder-LHS|<tuple|3.3|?>>
    <associate|full-adder-RHS|<tuple|3.2|?>>
    <associate|full-adder-spec|<tuple|3.1|?>>
    <associate|ss:AssertMerkleRoot|<tuple|4.3.2|?>>
    <associate|ss:BTDenotationalSemantics|<tuple|4.4.1.1|?>>
    <associate|ss:BTMerkleRoots|<tuple|4.4.1.2|?>>
    <associate|ss:BitcoinPrimitives|<tuple|9.3|?>>
    <associate|ss:BitcoinTransactions|<tuple|4.4.1|?>>
    <associate|ss:DAGs|<tuple|7.1|?>>
    <associate|ss:DenotationalSemanticsOfFullSimplicity|<tuple|9.2.4|?>>
    <associate|ss:ELDenotationalSemantics|<tuple|A.1|?>>
    <associate|ss:FreeMonadicDeserialization|<tuple|9.2.6.1|?>>
    <associate|ss:Haskell-CheckSigHash|<tuple|9.1.6.3|?>>
    <associate|ss:Haskell-DAG|<tuple|9.2.6.2|?>>
    <associate|ss:Haskell-Serialization|<tuple|9.2.6|?>>
    <associate|ss:IMR|<tuple|7.2.3|?>>
    <associate|ss:ListFunctors|<tuple|2.2.2|?>>
    <associate|ss:MonadZero|<tuple|2.3.4|?>>
    <associate|ss:RepresentingValuesAsCellArrays|<tuple|3.5.1|?>>
    <associate|ss:Serialization|<tuple|7.2|?>>
    <associate|ss:UniversalSignatureHashModes|<tuple|6.3|?>>
    <associate|ss:bitOps|<tuple|3.3.1|?>>
    <associate|ss:checkSigHashAll|<tuple|4.5.1|?>>
    <associate|ss:cmr|<tuple|3.7|?>>
    <associate|ss:coqArith|<tuple|8.3.2|?>>
    <associate|ss:coqInitial|<tuple|8.2.1|?>>
    <associate|ss:haskellLoop|<tuple|9.1.5.5|?>>
    <associate|ss:inflate|<tuple|7.1.2.2|?>>
    <associate|ss:monadicSemantics|<tuple|4.1|?>>
    <associate|ss:optionMonad|<tuple|2.3.4.1|?>>
    <associate|ss:pruning|<tuple|4.3.2.1|?>>
    <associate|ss:salted|<tuple|4.3.2.2|?>>
    <associate|ss:typeInference|<tuple|7.1.1|?>>
    <associate|ss:unboundedLoop|<tuple|6.2|?>>
    <associate|thm:CSCT|<tuple|3.3|?>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      bitcoin

      satoshiScript

      script

      Coq:manual

      King1993

      gentzen

      sha

      sec2

      libsecp256k1

      bip-0340

      unification

      Mairson:1989

      f-algebra

      Mahboubi:2013

      garillot:2009

      Appel:2015

      Carette:2009

      libsecp256k1

      bip-0340

      oconnor2014
    </associate>
    <\associate|figure>
      <tuple|normal|Example state of the Bit Machine.|<pageref|auto-55>>

      <tuple|normal|The inheritance hierarchy of algebras for Simplicity's
      partial extensions in Coq.|<pageref|auto-123>>
    </associate>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Introduction>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      1.1<space|2spc>Bitcoin Script <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2>

      1.2<space|2spc>Simplicity's Design Goals
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>

      <with|par-left|<quote|1tab>|1.2.1<space|2spc>Static Analysis
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <with|par-left|<quote|1tab>|1.2.2<space|2spc>Pruning and Sharing
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <with|par-left|<quote|1tab>|1.2.3<space|2spc>Formal Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Type
      Theory Preliminaries> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7><vspace|0.5fn>

      2.1<space|2spc>Algebraic Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>

      <with|par-left|<quote|1tab>|2.1.1<space|2spc>Records
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9>>

      2.2<space|2spc>Functors <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10>

      <with|par-left|<quote|1tab>|2.2.1<space|2spc>Option Functor
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <with|par-left|<quote|1tab>|2.2.2<space|2spc>List Functors
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12>>

      2.3<space|2spc>Monads <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13>

      <with|par-left|<quote|1tab>|2.3.1<space|2spc>Kleisli Morphisms
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14>>

      <with|par-left|<quote|1tab>|2.3.2<space|2spc>Cartesian Strength
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15>>

      <with|par-left|<quote|1tab>|2.3.3<space|2spc>Identity Monad
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-16>>

      <with|par-left|<quote|1tab>|2.3.4<space|2spc>Monad Zero
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-17>>

      <with|par-left|<quote|2tab>|2.3.4.1<space|2spc>Option Monad
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-18>>

      2.4<space|2spc>Multi-bit Words <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-19>

      <with|par-left|<quote|1tab>|2.4.1<space|2spc>Byte Strings
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-20>>

      <with|par-left|<quote|1tab>|2.4.2<space|2spc>Bit Strings
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-21>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Core
      Simplicity> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-22><vspace|0.5fn>

      3.1<space|2spc>Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-23>

      <with|par-left|<quote|1tab>|3.1.1<space|2spc>Abstract Syntax
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-24>>

      <with|par-left|<quote|1tab>|3.1.2<space|2spc>Formal Syntax
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-25>>

      <with|par-left|<quote|1tab>|3.1.3<space|2spc>Formal Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-26>>

      3.2<space|2spc>Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-27>

      <with|par-left|<quote|1tab>|3.2.1<space|2spc>Identity
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-28>>

      <with|par-left|<quote|1tab>|3.2.2<space|2spc>Composition
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-29>>

      <with|par-left|<quote|1tab>|3.2.3<space|2spc>Constant Unit
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-30>>

      <with|par-left|<quote|1tab>|3.2.4<space|2spc>Left Injection
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-31>>

      <with|par-left|<quote|1tab>|3.2.5<space|2spc>Right Injection
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-32>>

      <with|par-left|<quote|1tab>|3.2.6<space|2spc>Case
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-33>>

      <with|par-left|<quote|1tab>|3.2.7<space|2spc>Pair
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-34>>

      <with|par-left|<quote|1tab>|3.2.8<space|2spc>Take
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-35>>

      <with|par-left|<quote|1tab>|3.2.9<space|2spc>Drop
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-36>>

      <with|par-left|<quote|1tab>|3.2.10<space|2spc>Formal Syntax
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-37>>

      <with|par-left|<quote|1tab>|3.2.11<space|2spc>Formal Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-38>>

      3.3<space|2spc>Example Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-39>

      <with|par-left|<quote|1tab>|3.3.1<space|2spc>Bit Operations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-40>>

      <with|par-left|<quote|1tab>|3.3.2<space|2spc>Simplicity Notation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-41>>

      <with|par-left|<quote|1tab>|3.3.3<space|2spc>Generic Equality
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-42>>

      <with|par-left|<quote|1tab>|3.3.4<space|2spc>Arithmetic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-43>>

      <with|par-left|<quote|1tab>|3.3.5<space|2spc>Bitwise Operations
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-44>>

      <with|par-left|<quote|1tab>|3.3.6<space|2spc>SHA-256
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-45>>

      <with|par-left|<quote|2tab>|3.3.6.1<space|2spc>Tagged Hashes
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-46>>

      <with|par-left|<quote|1tab>|3.3.7<space|2spc>Elliptic Curve Operations
      on secp256k1 <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-47>>

      <with|par-left|<quote|2tab>|3.3.7.1<space|2spc>libsecp256k1
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-48>>

      <with|par-left|<quote|2tab>|3.3.7.2<space|2spc>libsecp256k1 in
      Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-49>>

      <with|par-left|<quote|2tab>|3.3.7.3<space|2spc>Schnorr Signature
      Validation <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-50>>

      3.4<space|2spc>Completeness Theorem
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-51>

      3.5<space|2spc>Operational Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-52>

      <with|par-left|<quote|1tab>|3.5.1<space|2spc>Representing Values as
      Cell Arrays <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-53>>

      <with|par-left|<quote|1tab>|3.5.2<space|2spc>Bit Machine
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-54>>

      <with|par-left|<quote|2tab>|3.5.2.1<space|2spc>Frame Instructions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-56>>

      <with|par-left|<quote|2tab>|3.5.2.2<space|2spc>Active Write Frame
      Instructions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-57>>

      <with|par-left|<quote|2tab>|3.5.2.3<space|2spc>Active Read Frame
      Instructions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-58>>

      <with|par-left|<quote|2tab>|3.5.2.4<space|2spc>Abort Instruction
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-59>>

      <with|par-left|<quote|2tab>|3.5.2.5<space|2spc>Bit Machine Programs
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-60>>

      <with|par-left|<quote|2tab>|3.5.2.6<space|2spc>Crashing the Bit Machine
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-61>>

      <with|par-left|<quote|1tab>|3.5.3<space|2spc>Executing Simplicity
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-62>>

      <with|par-left|<quote|2tab>|3.5.3.1<space|2spc>Tail Composition
      Optimisation (TCO) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-63>>

      3.6<space|2spc>Static Analysis <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-64>

      <with|par-left|<quote|1tab>|3.6.1<space|2spc>Space Resources
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-65>>

      <with|par-left|<quote|2tab>|3.6.1.1<space|2spc>Maximum Cell Count Bound
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-66>>

      <with|par-left|<quote|2tab>|3.6.1.2<space|2spc>Maximum Frame Count
      Bound <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-67>>

      <with|par-left|<quote|1tab>|3.6.2<space|2spc>Time Resources
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-68>>

      3.7<space|2spc>Commitment Merkle Root
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-69>

      3.8<space|2spc>Type Merkle Root <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-70>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Simplicity
      Extensions> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-71><vspace|0.5fn>

      4.1<space|2spc>Monadic Semantics <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-72>

      4.2<space|2spc>Witness <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-73>

      <with|par-left|<quote|1tab>|4.2.1<space|2spc>Elided Computation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-74>>

      <with|par-left|<quote|1tab>|4.2.2<space|2spc>Type Inference with
      Witness <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-75>>

      4.3<space|2spc>Assertions and Failure
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-76>

      <with|par-left|<quote|1tab>|4.3.1<space|2spc>Denotational Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-77>>

      <with|par-left|<quote|1tab>|4.3.2<space|2spc>Merkle Roots
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-78>>

      <with|par-left|<quote|2tab>|4.3.2.1<space|2spc>Pruning Unused
      <with|font-family|<quote|ss>|case> Branches
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-79>>

      <with|par-left|<quote|2tab>|4.3.2.2<space|2spc>Salted Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-80>>

      4.4<space|2spc>Blockchain Primitives
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-81>

      <with|par-left|<quote|1tab>|4.4.1<space|2spc>Bitcoin Transactions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-82>>

      <with|par-left|<quote|2tab>|4.4.1.1<space|2spc>Denotational Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-83>>

      <with|par-left|<quote|2tab>|4.4.1.2<space|2spc>Merkle Roots
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-84>>

      4.5<space|2spc>Simplicity Programs <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-85>

      <with|par-left|<quote|1tab>|4.5.1<space|2spc>Example:
      <rigid|<with|mode|<quote|text>|<with|font-family|<quote|ss>|font-shape|<quote|right>|checkSigHashAll>>>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-86>>

      4.6<space|2spc>Schnorr Signature Aggregation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-87>

      4.7<space|2spc>Malleability <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-88>

      <with|par-left|<quote|1tab>|4.7.1<space|2spc>Transaction Weight
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-89>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Jets>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-90><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Delegation>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-91><vspace|0.5fn>

      6.1<space|2spc>Implementing <with|font-family|<quote|ss>|disconnect> on
      the Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-92>

      <with|par-left|<quote|1tab>|6.1.1<space|2spc>Static Analysis of
      <with|font-family|<quote|ss>|disconnect>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-93>>

      <with|par-left|<quote|2tab>|6.1.1.1<space|2spc>Space Resources
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-94>>

      6.2<space|2spc>Unbounded Loops <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-95>

      <with|par-left|<quote|1tab>|6.2.1<space|2spc>Adding a
      <with|font-family|<quote|ss>|loop> primitive to Simplicity?
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-96>>

      6.3<space|2spc>Universal Signature Hash Modes
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-97>

      <with|par-left|<quote|1tab>|6.3.1<space|2spc>Side-Effects and
      Delegation <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-98>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|7<space|2spc>Type
      Inference and Serialization> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-99><vspace|0.5fn>

      7.1<space|2spc>Explicit Simplicity DAGs
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-100>

      <with|par-left|<quote|1tab>|7.1.1<space|2spc>Type Inference
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-101>>

      <with|par-left|<quote|1tab>|7.1.2<space|2spc>Reconstructing Simplicity
      Expressions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-102>>

      <with|par-left|<quote|2tab>|7.1.2.1<space|2spc>syncase
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-103>>

      <with|par-left|<quote|2tab>|7.1.2.2<space|2spc>inflate
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-104>>

      7.2<space|2spc>Serialization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-105>

      <with|par-left|<quote|1tab>|7.2.1<space|2spc>Serialization of Bit
      Strings and Positive Numbers <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-106>>

      <with|par-left|<quote|1tab>|7.2.2<space|2spc>Serialization of
      Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-107>>

      <with|par-left|<quote|1tab>|7.2.3<space|2spc>Identity Merkle Root
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-108>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|8<space|2spc>Coq
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-109><vspace|0.5fn>

      8.1<space|2spc>Simplicity Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-110>

      8.2<space|2spc>Simplicity Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-111>

      <with|par-left|<quote|1tab>|8.2.1<space|2spc>The ``Initial''
      Representation of Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-112>>

      <with|par-left|<quote|1tab>|8.2.2<space|2spc>The ``Final''
      Representation of Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-113>>

      <with|par-left|<quote|2tab>|8.2.2.1<space|2spc>Simplicity Algebras
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-114>>

      <with|par-left|<quote|2tab>|8.2.2.2<space|2spc>The ``Final''
      Representation <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-115>>

      <with|par-left|<quote|2tab>|8.2.2.3<space|2spc>Constructing ``Final''
      Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-116>>

      <with|par-left|<quote|1tab>|8.2.3<space|2spc>Why two representations of
      Terms? <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-117>>

      8.3<space|2spc>Example Simplicity Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-118>

      <with|par-left|<quote|1tab>|8.3.1<space|2spc>Bits
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-119>>

      <with|par-left|<quote|1tab>|8.3.2<space|2spc>Arithmetic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-120>>

      <with|par-left|<quote|1tab>|8.3.3<space|2spc>SHA256
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-121>>

      8.4<space|2spc>The Hierarchy of Simplicity Language Extensions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-122>

      <with|par-left|<quote|1tab>|8.4.1<space|2spc>Witness
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-124>>

      <with|par-left|<quote|1tab>|8.4.2<space|2spc>Assertion
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-125>>

      <with|par-left|<quote|1tab>|8.4.3<space|2spc>Delegation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-126>>

      <with|par-left|<quote|1tab>|8.4.4<space|2spc>Primitives
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-127>>

      <with|par-left|<quote|2tab>|8.4.4.1<space|2spc>Bitcoin
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-128>>

      <with|par-left|<quote|1tab>|8.4.5<space|2spc>Jets
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-129>>

      <with|par-left|<quote|1tab>|8.4.6<space|2spc>Full Simplicity
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-130>>

      8.5<space|2spc>Merkle Roots <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-131>

      8.6<space|2spc>The Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-132>

      <with|par-left|<quote|1tab>|8.6.1<space|2spc>Bit Machine Code
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-133>>

      <with|par-left|<quote|2tab>|8.6.1.1<space|2spc>Bit Machine Programs
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-134>>

      <with|par-left|<quote|1tab>|8.6.2<space|2spc>Translating Simplicity to
      the Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-135>>

      <with|par-left|<quote|1tab>|8.6.3<space|2spc>Static Analysis
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-136>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|9<space|2spc>Haskell
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-137><vspace|0.5fn>

      9.1<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|Simplicity-Core>
      library <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-138>

      <with|par-left|<quote|1tab>|9.1.1<space|2spc>Simplicity Types
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-139>>

      <with|par-left|<quote|1tab>|9.1.2<space|2spc>Simplicity Terms
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-140>>

      <with|par-left|<quote|1tab>|9.1.3<space|2spc>Merkle Roots
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-141>>

      <with|par-left|<quote|1tab>|9.1.4<space|2spc>Tensors
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-142>>

      <with|par-left|<quote|1tab>|9.1.5<space|2spc>Example Simplicity
      Expressions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-143>>

      <with|par-left|<quote|2tab>|9.1.5.1<space|2spc>Generic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-144>>

      <with|par-left|<quote|2tab>|9.1.5.2<space|2spc>Bits
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-145>>

      <with|par-left|<quote|2tab>|9.1.5.3<space|2spc>Multi-bit Words
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-146>>

      <with|par-left|<quote|2tab>|9.1.5.4<space|2spc>Arithmetic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-147>>

      <with|par-left|<quote|2tab>|9.1.5.5<space|2spc>Loop
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-148>>

      <with|par-left|<quote|1tab>|9.1.6<space|2spc>Libraries of Simplicity
      Expressions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-149>>

      <with|par-left|<quote|2tab>|9.1.6.1<space|2spc>SHA-256
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-150>>

      <with|par-left|<quote|2tab>|9.1.6.2<space|2spc>LibSecp256k1
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-151>>

      <with|par-left|<quote|2tab>|9.1.6.3<space|2spc>CheckSigHash
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-152>>

      <with|par-left|<quote|1tab>|9.1.7<space|2spc>The Bit Machine
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-153>>

      <with|par-left|<quote|2tab>|9.1.7.1<space|2spc>Translating Simplicity
      to the Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-154>>

      <with|par-left|<quote|2tab>|9.1.7.2<space|2spc>Static Analysis
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-155>>

      <with|par-left|<quote|2tab>|9.1.7.3<space|2spc>Fast Evaluation with FFI
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-156>>

      9.2<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|Simplicity-Indef>
      library <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-157>

      <with|par-left|<quote|1tab>|9.2.1<space|2spc>Primitive Signature
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-158>>

      <with|par-left|<quote|1tab>|9.2.2<space|2spc>Primitive Terms
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-159>>

      <with|par-left|<quote|1tab>|9.2.3<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|JetType>
      class <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-160>>

      <with|par-left|<quote|1tab>|9.2.4<space|2spc>Denotational Semantics of
      Full Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-161>>

      <with|par-left|<quote|1tab>|9.2.5<space|2spc>Type Inference
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-162>>

      <with|par-left|<quote|1tab>|9.2.6<space|2spc>Serialization
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-163>>

      <with|par-left|<quote|2tab>|9.2.6.1<space|2spc>Free Monadic
      Deserializaiton <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-164>>

      <with|par-left|<quote|2tab>|9.2.6.2<space|2spc>Serialization of
      Simplicity DAGs <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-165>>

      <with|par-left|<quote|1tab>|9.2.7<space|2spc>Jet Substitution
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-166>>

      9.3<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|Simplicity-Bitcoin>
      Libary <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-167>

      9.4<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|Simplicity>
      Library <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-168>

      <with|par-left|<quote|1tab>|9.4.1<space|2spc>CheckSigHashAll
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-169>>

      <with|par-left|<quote|1tab>|9.4.2<space|2spc>Known Discounted Jets
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-170>>

      9.5<space|2spc>Simplicity <with|font-family|<quote|tt>|language|<quote|verbatim>|testsuite>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-171>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|10<space|2spc>C
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-172><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Appendix
      A<space|2spc>Elements Application> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-173><vspace|0.5fn>

      A.1<space|2spc>Denotational Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-174>

      <with|par-left|<quote|1tab>|A.1.1<space|2spc>Null Data
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-175>>

      <with|par-left|<quote|1tab>|A.1.2<space|2spc>Merkle Roots
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-176>>

      <with|par-left|<quote|1tab>|A.1.3<space|2spc>Serialization
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-177>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Appendix
      B<space|2spc>Catelogue of Jets> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-178><vspace|0.5fn>

      B.1<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|110...:
      >Core Jets <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-179>

      <with|par-left|<quote|1tab>|B.1.1<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|1100...:
      >Jets for multi-bit logic <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-180>>

      <with|par-left|<quote|2tab>|B.1.1.1<space|2spc><with|font-family|<quote|ss>|low>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-181>>

      <with|par-left|<quote|2tab>|B.1.1.2<space|2spc><with|font-family|<quote|ss>|high>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-182>>

      <with|par-left|<quote|2tab>|B.1.1.3<space|2spc><with|font-family|<quote|ss>|complement>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-183>>

      <with|par-left|<quote|2tab>|B.1.1.4<space|2spc><with|font-family|<quote|ss>|and>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-184>>

      <with|par-left|<quote|2tab>|B.1.1.5<space|2spc><with|font-family|<quote|ss>|or>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-185>>

      <with|par-left|<quote|2tab>|B.1.1.6<space|2spc><with|font-family|<quote|ss>|xor>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-186>>

      <with|par-left|<quote|2tab>|B.1.1.7<space|2spc><with|font-family|<quote|ss>|maj>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-187>>

      <with|par-left|<quote|2tab>|B.1.1.8<space|2spc><with|font-family|<quote|ss>|xor3>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-188>>

      <with|par-left|<quote|2tab>|B.1.1.9<space|2spc><with|font-family|<quote|ss>|ch>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-189>>

      <with|par-left|<quote|2tab>|B.1.1.10<space|2spc><with|font-family|<quote|ss>|some>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-190>>

      <with|par-left|<quote|2tab>|B.1.1.11<space|2spc><with|font-family|<quote|ss>|all>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-191>>

      <with|par-left|<quote|2tab>|B.1.1.12<space|2spc><with|font-family|<quote|ss>|eq>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-192>>

      <with|par-left|<quote|2tab>|B.1.1.13<space|2spc><with|font-family|<quote|ss>|full-left-shift>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-193>>

      <with|par-left|<quote|2tab>|B.1.1.14<space|2spc><with|font-family|<quote|ss>|full-right-shift>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-194>>

      <with|par-left|<quote|2tab>|B.1.1.15<space|2spc><with|font-family|<quote|ss>|leftmost>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-195>>

      <with|par-left|<quote|2tab>|B.1.1.16<space|2spc><with|font-family|<quote|ss>|rightmost>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-196>>

      <with|par-left|<quote|2tab>|B.1.1.17<space|2spc><with|font-family|<quote|ss>|left-pad-low>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-197>>

      <with|par-left|<quote|2tab>|B.1.1.18<space|2spc><with|font-family|<quote|ss>|left-pad-high>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-198>>

      <with|par-left|<quote|2tab>|B.1.1.19<space|2spc><with|font-family|<quote|ss>|left-extend>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-199>>

      <with|par-left|<quote|2tab>|B.1.1.20<space|2spc><with|font-family|<quote|ss>|right-pad-low>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-200>>

      <with|par-left|<quote|2tab>|B.1.1.21<space|2spc><with|font-family|<quote|ss>|right-pad-high>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-201>>

      <with|par-left|<quote|2tab>|B.1.1.22<space|2spc><with|font-family|<quote|ss>|right-extend>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-202>>

      <with|par-left|<quote|2tab>|B.1.1.23<space|2spc><with|font-family|<quote|ss>|right-shift-with>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-203>>

      <with|par-left|<quote|2tab>|B.1.1.24<space|2spc><with|font-family|<quote|ss>|right-shift>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-204>>

      <with|par-left|<quote|2tab>|B.1.1.25<space|2spc><with|font-family|<quote|ss>|right-rotate>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-205>>

      <with|par-left|<quote|2tab>|B.1.1.26<space|2spc><with|font-family|<quote|ss>|transpose>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-206>>

      <with|par-left|<quote|2tab>|B.1.1.27<space|2spc><with|font-family|<quote|ss>|find-first-high>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-207>>

      <with|par-left|<quote|2tab>|B.1.1.28<space|2spc><with|font-family|<quote|ss>|find-last-high>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-208>>

      <with|par-left|<quote|2tab>|B.1.1.29<space|2spc><with|font-family|<quote|ss>|bit>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-209>>

      <with|par-left|<quote|1tab>|B.1.2<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|110100...:
      >Jets for arithmetic <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-210>>

      <with|par-left|<quote|2tab>|B.1.2.1<space|2spc><with|font-family|<quote|ss>|one>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-211>>

      <with|par-left|<quote|2tab>|B.1.2.2<space|2spc><with|font-family|<quote|ss>|full-add>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-212>>

      <with|par-left|<quote|2tab>|B.1.2.3<space|2spc><with|font-family|<quote|ss>|add>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-213>>

      <with|par-left|<quote|2tab>|B.1.2.4<space|2spc><with|font-family|<quote|ss>|full-increment>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-214>>

      <with|par-left|<quote|2tab>|B.1.2.5<space|2spc><with|font-family|<quote|ss>|increment>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-215>>

      <with|par-left|<quote|2tab>|B.1.2.6<space|2spc><with|font-family|<quote|ss>|popcount>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-216>>

      <with|par-left|<quote|2tab>|B.1.2.7<space|2spc><with|font-family|<quote|ss>|full-subtract>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-217>>

      <with|par-left|<quote|2tab>|B.1.2.8<space|2spc><with|font-family|<quote|ss>|subtract>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-218>>

      <with|par-left|<quote|2tab>|B.1.2.9<space|2spc><with|font-family|<quote|ss>|negate>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-219>>

      <with|par-left|<quote|2tab>|B.1.2.10<space|2spc><with|font-family|<quote|ss>|full-decrement>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-220>>

      <with|par-left|<quote|2tab>|B.1.2.11<space|2spc><with|font-family|<quote|ss>|decrement>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-221>>

      <with|par-left|<quote|2tab>|B.1.2.12<space|2spc><with|font-family|<quote|ss>|full-multiply>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-222>>

      <with|par-left|<quote|2tab>|B.1.2.13<space|2spc><with|font-family|<quote|ss>|multiply>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-223>>

      <with|par-left|<quote|2tab>|B.1.2.14<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|><with|font-family|<quote|ss>|is-zero>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-224>>

      <with|par-left|<quote|2tab>|B.1.2.15<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|><with|font-family|<quote|ss>|is-one>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-225>>

      <with|par-left|<quote|2tab>|B.1.2.16<space|2spc><with|font-family|<quote|ss>|le>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-226>>

      <with|par-left|<quote|2tab>|B.1.2.17<space|2spc><with|font-family|<quote|ss>|lt>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-227>>

      <with|par-left|<quote|2tab>|B.1.2.18<space|2spc><with|font-family|<quote|ss>|min>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-228>>

      <with|par-left|<quote|2tab>|B.1.2.19<space|2spc><with|font-family|<quote|ss>|max>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-229>>

      <with|par-left|<quote|2tab>|B.1.2.20<space|2spc><with|font-family|<quote|ss>|median>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-230>>

      <with|par-left|<quote|2tab>|B.1.2.21<space|2spc><with|font-family|<quote|ss>|div2n1n>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-231>>

      <with|par-left|<quote|2tab>|B.1.2.22<space|2spc><with|font-family|<quote|ss>|div-mod>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-232>>

      <with|par-left|<quote|2tab>|B.1.2.23<space|2spc><with|font-family|<quote|ss>|divide>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-233>>

      <with|par-left|<quote|2tab>|B.1.2.24<space|2spc><with|font-family|<quote|ss>|modulo>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-234>>

      <with|par-left|<quote|2tab>|B.1.2.25<space|2spc><with|font-family|<quote|ss>|divides>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-235>>

      <with|par-left|<quote|2tab>|B.1.2.26<space|2spc><with|font-family|<quote|ss>|eea>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-236>>

      <with|par-left|<quote|2tab>|B.1.2.27<space|2spc><with|font-family|<quote|ss>|bezout>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-237>>

      <with|par-left|<quote|2tab>|B.1.2.28<space|2spc><with|font-family|<quote|ss>|gcd>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-238>>

      <with|par-left|<quote|2tab>|B.1.2.29<space|2spc><with|font-family|<quote|ss>|cofactors>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-239>>

      <with|par-left|<quote|2tab>|B.1.2.30<space|2spc><with|font-family|<quote|ss>|lcm>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-240>>

      <with|par-left|<quote|2tab>|B.1.2.31<space|2spc><with|font-family|<quote|ss>|jacobi>
      (unsigned) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-241>>

      <with|par-left|<quote|2tab>|B.1.2.32<space|2spc><with|font-family|<quote|ss>|absolute-value>
      (signed input/unsigned output) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-242>>

      <with|par-left|<quote|2tab>|B.1.2.33<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|><with|font-family|<quote|ss>|sign>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-243>>

      <with|par-left|<quote|2tab>|B.1.2.34<space|2spc><with|font-family|<quote|ss>|signed-le>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-244>>

      <with|par-left|<quote|2tab>|B.1.2.35<space|2spc><with|font-family|<quote|ss>|signed-lt>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-245>>

      <with|par-left|<quote|2tab>|B.1.2.36<space|2spc><with|font-family|<quote|ss>|signed-min>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-246>>

      <with|par-left|<quote|2tab>|B.1.2.37<space|2spc><with|font-family|<quote|ss>|signed-max>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-247>>

      <with|par-left|<quote|2tab>|B.1.2.38<space|2spc><with|font-family|<quote|ss>|signed-median>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-248>>

      <with|par-left|<quote|2tab>|B.1.2.39<space|2spc><with|font-family|<quote|ss>|signed-right-shift>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-249>>

      <with|par-left|<quote|2tab>|B.1.2.40<space|2spc><with|font-family|<quote|ss>|signed-divmod>
      (unsigned denominator) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-250>>

      <with|par-left|<quote|2tab>|B.1.2.41<space|2spc><with|font-family|<quote|ss>|signed-div>
      (unsigned denominator) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-251>>

      <with|par-left|<quote|2tab>|B.1.2.42<space|2spc><with|font-family|<quote|ss>|signed-signed-divmod>
      (signed denominator) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-252>>

      <with|par-left|<quote|2tab>|B.1.2.43<space|2spc><with|font-family|<quote|ss>|signed-signed-div>
      (signed denominator) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-253>>

      <with|par-left|<quote|1tab>|B.1.3<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|110101...:
      >Jets for hash functions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-254>>

      <with|par-left|<quote|2tab>|B.1.3.1<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|1101010...:
      >Jets for SHA-2 <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-255>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|sha-256-block>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-256><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|sha-256-iv>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-257><vspace|0.15fn>>

      <with|par-left|<quote|2tab>|B.1.3.2<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|110101100...:
      >Jets for SHA-3 <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-258>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|sha3-zero>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-259><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|sha3-absorb>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-260><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|sha3-xor>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-261><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|sha3-permute>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-262><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|sha3-squeeze-256>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-263><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|sha3-squeeze-512>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-264><vspace|0.15fn>>

      <with|par-left|<quote|2tab>|B.1.3.3<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|110101101...:
      >Jets for RIPEMD <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-265>>

      <with|par-left|<quote|2tab>|B.1.3.4<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|110101110000...:
      >Jets for SHA-1 (RESERVED) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-266>>

      <with|par-left|<quote|1tab>|B.1.4<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|110110000...:
      >Jets for elliptic curve functions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-267>>

      <with|par-left|<quote|2tab>|B.1.4.1<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|1101100000...:
      >Jets for secp256k1 <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-268>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-point-verify>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-269><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-decompress>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-270><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-linear-verify>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-271><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-linear-combination>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-272><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-scale>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-273><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-generate>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-274><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-infinity>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-275><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-normalize>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-276><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-negate>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-277><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-ge-negate>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-278><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-double>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-279><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-add>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-280><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-ge-add-ex>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-281><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-ge-add>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-282><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-is-infinity>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-283><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-equiv>
      <with|color|<quote|red>|Does not exist in libsecp256k1>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-284><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-ge-equiv>
      <with|color|<quote|red>|Does not exist in libsecp256k1>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-285><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-x-equiv>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-286><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-y-is-odd>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-287><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-is-on-curve>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-288><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-ge-is-on-curve>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-289><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-scalar-normalize>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-290><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-scalar-negate>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-291><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-scalar-add>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-292><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-scalar-square>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-293><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-scalar-multiply>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-294><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-scalar-multiply-lambda>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-295><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-scalar-invert>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-296><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-scalar-is-zero>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-297><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-ge-scale-lambda>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-298><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-gej-scale-lambda>
      <with|color|<quote|red>|Consider removing>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-299><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-scalar-split-lambda>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-300><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-short-scalar>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-301><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-fe-normalize>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-302><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-fe-negate>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-303><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-fe-add>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-304><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-fe-square>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-305><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-fe-multiply>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-306><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-fe-multiply-beta>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-307><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-fe-invert>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-308><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-fe-square-root>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-309><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-fe-is-zero>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-310><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-fe-is-odd>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-311><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-fe-is-quad>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-312><vspace|0.15fn>>

      <with|par-left|<quote|1tab>|B.1.5<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|110110001...:
      >Jets for digital signatures <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-313>>

      <with|par-left|<quote|2tab>|B.1.5.1<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|1101100010...:
      >Jets for secp256k1 based digital signatures
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-314>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|bip0340-schnorr-verify>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-315><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|bip0340-challenge-iv>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-316><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|bip0340-challenge-midstate>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-317><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-signature-unpack>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-318><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-pubkey-unpack>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-319><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-pubkey-unpack-neg>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-320><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|secp256k1-ecdsa>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-321><vspace|0.15fn>>

      <with|par-left|<quote|1tab>|B.1.6<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|110110010...:
      >Jets for Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-322>>

      <with|par-left|<quote|2tab>|B.1.6.1<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|11011000100...:
      >Jets for tagged hash IVs <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-323>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|iden-commitment-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-324><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|comp-commitment-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-325><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|unit-commitment-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-326><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|injl-commitment-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-327><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|injr-commitment-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-328><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|case-commitment-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-329><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|pair-commitment-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-330><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|take-commitment-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-331><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|drop-commitment-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-332><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|witness-commitment-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-333><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|disconnect-commitment-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-334><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|fail-commitment-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-335><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|signtaure-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-336><vspace|0.15fn>>

      <with|par-left|<quote|4tab>|<with|font-family|<quote|ss>|sighash-tag>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-337><vspace|0.15fn>>

      <with|par-left|<quote|1tab>|B.1.7<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|110110011...:
      >Jets for Bitcoin (without primitives)
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-338>>

      <with|par-left|<quote|2tab>|B.1.7.1<space|2spc><with|font-family|<quote|ss>|parse-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-339>>

      <with|par-left|<quote|2tab>|B.1.7.2<space|2spc><with|font-family|<quote|ss>|parse-sequence>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-340>>

      <with|par-left|<quote|1tab>|B.1.8<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|1101101000...:
      >Jets for Elements (without primitives)
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-341>>

      <with|par-left|<quote|2tab>|B.1.8.1<space|2spc><with|font-family|<quote|ss>|generate-entropy>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-342>>

      <with|par-left|<quote|2tab>|B.1.8.2<space|2spc><with|font-family|<quote|ss>|calculate-asset>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-343>>

      <with|par-left|<quote|2tab>|B.1.8.3<space|2spc><with|font-family|<quote|ss>|calculate-token>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-344>>

      B.2<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|111...:
      >Bitcoin Jets <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-345>

      <with|par-left|<quote|1tab>|B.2.1<space|2spc>Transaction
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-346>>

      <with|par-left|<quote|1tab>|B.2.2<space|2spc>Signature Hash Modes
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-347>>

      <with|par-left|<quote|1tab>|B.2.3<space|2spc>Time Locks
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-348>>

      <with|par-left|<quote|2tab>|B.2.3.1<space|2spc><with|font-family|<quote|ss>|total-height-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-349>>

      <with|par-left|<quote|2tab>|B.2.3.2<space|2spc><with|font-family|<quote|ss>|total-time-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-350>>

      <with|par-left|<quote|2tab>|B.2.3.3<space|2spc><with|font-family|<quote|ss>|total-distance-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-351>>

      <with|par-left|<quote|2tab>|B.2.3.4<space|2spc><with|font-family|<quote|ss>|total-duration-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-352>>

      <with|par-left|<quote|2tab>|B.2.3.5<space|2spc><with|font-family|<quote|ss>|is-final>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-353>>

      <with|par-left|<quote|2tab>|B.2.3.6<space|2spc><with|font-family|<quote|ss>|current-height-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-354>>

      <with|par-left|<quote|2tab>|B.2.3.7<space|2spc><with|font-family|<quote|ss>|current-time-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-355>>

      <with|par-left|<quote|2tab>|B.2.3.8<space|2spc><with|font-family|<quote|ss>|current-distance-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-356>>

      <with|par-left|<quote|2tab>|B.2.3.9<space|2spc><with|font-family|<quote|ss>|current-duration-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-357>>

      <with|par-left|<quote|2tab>|B.2.3.10<space|2spc><with|font-family|<quote|ss>|current-is-Final>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-358>>

      <with|par-left|<quote|2tab>|B.2.3.11<space|2spc><with|font-family|<quote|ss>|input-height-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-359>>

      <with|par-left|<quote|2tab>|B.2.3.12<space|2spc><with|font-family|<quote|ss>|input-time-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-360>>

      <with|par-left|<quote|2tab>|B.2.3.13<space|2spc><with|font-family|<quote|ss>|input-distance-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-361>>

      <with|par-left|<quote|2tab>|B.2.3.14<space|2spc><with|font-family|<quote|ss>|input-duration-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-362>>

      <with|par-left|<quote|2tab>|B.2.3.15<space|2spc><with|font-family|<quote|ss>|input-is-final>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-363>>

      B.3<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|111...:
      >Elements Jets <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-364>

      <with|par-left|<quote|1tab>|B.3.1<space|2spc>Transaction
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-365>>

      <with|par-left|<quote|1tab>|B.3.2<space|2spc>Time Locks
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-366>>

      <with|par-left|<quote|2tab>|B.3.2.1<space|2spc><with|font-family|<quote|ss>|total-height-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-367>>

      <with|par-left|<quote|2tab>|B.3.2.2<space|2spc><with|font-family|<quote|ss>|total-time-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-368>>

      <with|par-left|<quote|2tab>|B.3.2.3<space|2spc><with|font-family|<quote|ss>|total-distance-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-369>>

      <with|par-left|<quote|2tab>|B.3.2.4<space|2spc><with|font-family|<quote|ss>|total-duration-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-370>>

      <with|par-left|<quote|2tab>|B.3.2.5<space|2spc><with|font-family|<quote|ss>|is-final>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-371>>

      <with|par-left|<quote|2tab>|B.3.2.6<space|2spc><with|font-family|<quote|ss>|current-height-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-372>>

      <with|par-left|<quote|2tab>|B.3.2.7<space|2spc><with|font-family|<quote|ss>|current-time-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-373>>

      <with|par-left|<quote|2tab>|B.3.2.8<space|2spc><with|font-family|<quote|ss>|current-distance-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-374>>

      <with|par-left|<quote|2tab>|B.3.2.9<space|2spc><with|font-family|<quote|ss>|current-duration-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-375>>

      <with|par-left|<quote|2tab>|B.3.2.10<space|2spc><with|font-family|<quote|ss>|current-is-Final>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-376>>

      <with|par-left|<quote|2tab>|B.3.2.11<space|2spc><with|font-family|<quote|ss>|input-height-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-377>>

      <with|par-left|<quote|2tab>|B.3.2.12<space|2spc><with|font-family|<quote|ss>|input-time-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-378>>

      <with|par-left|<quote|2tab>|B.3.2.13<space|2spc><with|font-family|<quote|ss>|input-distance-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-379>>

      <with|par-left|<quote|2tab>|B.3.2.14<space|2spc><with|font-family|<quote|ss>|input-duration-lock>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-380>>

      <with|par-left|<quote|2tab>|B.3.2.15<space|2spc><with|font-family|<quote|ss>|input-is-final>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-381>>

      <with|par-left|<quote|1tab>|B.3.3<space|2spc>Issuance
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-382>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Appendix
      C<space|2spc>Alternative Serialization of Simplicity DAGs>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-383><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-384><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>