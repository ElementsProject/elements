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

    <with|par-left|1tab|3.3.7<space|2spc>Elliptic Curve Operations on
    secp256k1 <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-46>>

    <with|par-left|2tab|3.3.7.1<space|2spc>libsecp256k1
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-47>>

    <with|par-left|2tab|3.3.7.2<space|2spc>libsecp256k1 in Simplicity
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-48>>

    <with|par-left|2tab|3.3.7.3<space|2spc>Schnorr Signature Validation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-49>>

    3.4<space|2spc>Completeness Theorem <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-50>

    3.5<space|2spc>Operational Semantics <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-51>

    <with|par-left|1tab|3.5.1<space|2spc>Representing Values as Cell Arrays
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-52>>

    <with|par-left|1tab|3.5.2<space|2spc>Bit Machine
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-53>>

    <with|par-left|2tab|3.5.2.1<space|2spc>Frame Instructions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-55>>

    <with|par-left|2tab|3.5.2.2<space|2spc>Active Write Frame Instructions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-56>>

    <with|par-left|2tab|3.5.2.3<space|2spc>Active Read Frame Instructions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-57>>

    <with|par-left|2tab|3.5.2.4<space|2spc>Abort Instruction
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-58>>

    <with|par-left|2tab|3.5.2.5<space|2spc>Bit Machine Programs
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-59>>

    <with|par-left|2tab|3.5.2.6<space|2spc>Crashing the Bit Machine
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-60>>

    <with|par-left|1tab|3.5.3<space|2spc>Executing Simplicity
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-61>>

    <with|par-left|2tab|3.5.3.1<space|2spc>Tail Composition Optimisation
    (TCO) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-62>>

    3.6<space|2spc>Static Analysis <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-63>

    <with|par-left|1tab|3.6.1<space|2spc>Space Resources
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-64>>

    <with|par-left|2tab|3.6.1.1<space|2spc>Maximum Cell Count Bound
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-65>>

    <with|par-left|2tab|3.6.1.2<space|2spc>Maximum Frame Count Bound
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-66>>

    <with|par-left|1tab|3.6.2<space|2spc>Time Resources
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-67>>

    3.7<space|2spc>Commitment Merkle Root
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-68>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|4<space|2spc>Simplicity
    Extensions> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-69><vspace|0.5fn>

    4.1<space|2spc>Monadic Semantics <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-70>

    4.2<space|2spc>Witness <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-71>

    <with|par-left|1tab|4.2.1<space|2spc>Elided Computation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-72>>

    <with|par-left|1tab|4.2.2<space|2spc>Witness Merkle Root
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-73>>

    <with|par-left|1tab|4.2.3<space|2spc>Type Inference with Witness
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-74>>

    4.3<space|2spc>Assertions and Failure
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-75>

    <with|par-left|1tab|4.3.1<space|2spc>Denotational Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-76>>

    <with|par-left|1tab|4.3.2<space|2spc>Merkle Roots
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-77>>

    <with|par-left|2tab|4.3.2.1<space|2spc>Pruning Unused
    <with|font-family|ss|case> Branches <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-78>>

    <with|par-left|2tab|4.3.2.2<space|2spc>Salted Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-79>>

    4.4<space|2spc>Blockchain Primitives <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-80>

    <with|par-left|1tab|4.4.1<space|2spc>Bitcoin Transactions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-81>>

    <with|par-left|2tab|4.4.1.1<space|2spc>Denotational Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-82>>

    <with|par-left|2tab|4.4.1.2<space|2spc>Merkle Roots
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-83>>

    4.5<space|2spc>Simplicity Programs <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-84>

    <with|par-left|1tab|4.5.1<space|2spc>Example:
    <rigid|<with|mode|text|<with|font-family|ss|font-shape|right|checkSigHashAll>>>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-85>>

    4.6<space|2spc>Schnorr Signature Aggregation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-86>

    4.7<space|2spc>Malleability <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-87>

    <with|par-left|1tab|4.7.1<space|2spc>Transaction Weight
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-88>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|5<space|2spc>Jets>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-89><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|6<space|2spc>Delegation>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-90><vspace|0.5fn>

    6.1<space|2spc>Unbounded Loops <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-91>

    <with|par-left|1tab|6.1.1<space|2spc>Adding a <with|font-family|ss|loop>
    primitive to Simplicity? <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-92>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|7<space|2spc>Type
    Inference and Serialization> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-93><vspace|0.5fn>

    7.1<space|2spc>Explicit Simplicity DAGs
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-94>

    <with|par-left|1tab|7.1.1<space|2spc>Type Inference
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-95>>

    <with|par-left|1tab|7.1.2<space|2spc>Reconstructing Simplicity
    Expressions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-96>>

    <with|par-left|2tab|7.1.2.1<space|2spc>syncase
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-97>>

    <with|par-left|2tab|7.1.2.2<space|2spc>inflate
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-98>>

    7.2<space|2spc>Serialization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-99>

    <with|par-left|1tab|7.2.1<space|2spc>Serialization of Bit Strings and
    Positive Numbers <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-100>>

    <with|par-left|1tab|7.2.2<space|2spc>Serialization of Simplicity
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-101>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|8<space|2spc>Coq
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-102><vspace|0.5fn>

    8.1<space|2spc>Simplicity Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-103>

    8.2<space|2spc>Simplicity Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-104>

    <with|par-left|1tab|8.2.1<space|2spc>The ``Initial'' Representation of
    Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-105>>

    <with|par-left|1tab|8.2.2<space|2spc>The ``Final'' Representation of
    Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-106>>

    <with|par-left|2tab|8.2.2.1<space|2spc>Simplicity Algebras
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-107>>

    <with|par-left|2tab|8.2.2.2<space|2spc>The ``Final'' Representation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-108>>

    <with|par-left|2tab|8.2.2.3<space|2spc>Constructing ``Final'' Terms
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-109>>

    <with|par-left|1tab|8.2.3<space|2spc>Why two representations of Terms?
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-110>>

    8.3<space|2spc>Example Simplicity Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-111>

    <with|par-left|1tab|8.3.1<space|2spc>Bits
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-112>>

    <with|par-left|1tab|8.3.2<space|2spc>Arithmetic
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-113>>

    <with|par-left|1tab|8.3.3<space|2spc>SHA256
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-114>>

    8.4<space|2spc>The Hierarchy of Simplicity Language Extensions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-115>

    <with|par-left|1tab|8.4.1<space|2spc>Witness
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-117>>

    <with|par-left|1tab|8.4.2<space|2spc>Assertion
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-118>>

    <with|par-left|1tab|8.4.3<space|2spc>Delegation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-119>>

    <with|par-left|1tab|8.4.4<space|2spc>Primitives
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-120>>

    <with|par-left|2tab|8.4.4.1<space|2spc>Bitcoin
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-121>>

    <with|par-left|1tab|8.4.5<space|2spc>Jets
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-122>>

    <with|par-left|1tab|8.4.6<space|2spc>Full Simplicity
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-123>>

    8.5<space|2spc>Merkle Roots <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-124>

    8.6<space|2spc>The Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-125>

    <with|par-left|1tab|8.6.1<space|2spc>Bit Machine Code
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-126>>

    <with|par-left|2tab|8.6.1.1<space|2spc>Bit Machine Programs
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-127>>

    <with|par-left|1tab|8.6.2<space|2spc>Translating Simplicity to the Bit
    Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-128>>

    <with|par-left|1tab|8.6.3<space|2spc>Static Analysis
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-129>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|9<space|2spc>Haskell
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-130><vspace|0.5fn>

    9.1<space|2spc><with|font-family|tt|language|verbatim|Simplicity-Core>
    library <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-131>

    <with|par-left|1tab|9.1.1<space|2spc>Simplicity Types
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-132>>

    <with|par-left|1tab|9.1.2<space|2spc>Simplicity Terms
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-133>>

    <with|par-left|1tab|9.1.3<space|2spc>Merkle Roots
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-134>>

    <with|par-left|1tab|9.1.4<space|2spc>Tensors
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-135>>

    <with|par-left|1tab|9.1.5<space|2spc>Example Simplicity Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-136>>

    <with|par-left|2tab|9.1.5.1<space|2spc>Bits
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-137>>

    <with|par-left|2tab|9.1.5.2<space|2spc>Multi-bit Words
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-138>>

    <with|par-left|2tab|9.1.5.3<space|2spc>Generic
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-139>>

    <with|par-left|2tab|9.1.5.4<space|2spc>Loop
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-140>>

    <with|par-left|1tab|9.1.6<space|2spc>Libraries of Simplicity Expressions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-141>>

    <with|par-left|2tab|9.1.6.1<space|2spc>SHA-256
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-142>>

    <with|par-left|2tab|9.1.6.2<space|2spc>LibSecp256k1
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-143>>

    <with|par-left|1tab|9.1.7<space|2spc>The Bit Machine
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-144>>

    <with|par-left|2tab|9.1.7.1<space|2spc>Translating Simplicity to the Bit
    Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-145>>

    <with|par-left|2tab|9.1.7.2<space|2spc>Static Analysis
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-146>>

    9.2<space|2spc><with|font-family|tt|language|verbatim|Simplicity-Indef>
    library <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-147>

    <with|par-left|1tab|9.2.1<space|2spc>Primitive Signature
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-148>>

    <with|par-left|1tab|9.2.2<space|2spc>Primitive Terms
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-149>>

    <with|par-left|1tab|9.2.3<space|2spc>Denotational Semantics of Full
    Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-150>>

    <with|par-left|1tab|9.2.4<space|2spc>Known Discounted Jets
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-151>>

    <with|par-left|1tab|9.2.5<space|2spc>Type Inference
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-152>>

    <with|par-left|1tab|9.2.6<space|2spc>Serialization
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-153>>

    <with|par-left|2tab|9.2.6.1<space|2spc>Free Monadic Deserializaiton
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-154>>

    <with|par-left|2tab|9.2.6.2<space|2spc>Serialization of Simplicity DAGs
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-155>>

    9.3<space|2spc><with|font-family|tt|language|verbatim|Simplicity-Bitcoin>
    Libary <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-156>

    9.4<space|2spc><with|font-family|tt|language|verbatim|Simplicity> Library
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-157>

    <with|par-left|1tab|9.4.1<space|2spc>CheckSigHashAll
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-158>>

    9.5<space|2spc>Simplicity <with|font-family|tt|language|verbatim|testsuite>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-159>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|10<space|2spc>C
    Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-160><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|Appendix
    A<space|2spc>Elements Application> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-161><vspace|0.5fn>

    A.1<space|2spc>Denotational Semantics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-162>

    <with|par-left|1tab|A.1.1<space|2spc>Null Data
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-163>>

    <with|par-left|1tab|A.1.2<space|2spc>Merkle Roots
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-164>>

    <with|par-left|1tab|A.1.3<space|2spc>Serialization
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-165>>

    A.2<space|2spc>Jets <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-166>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|Appendix
    B<space|2spc>Alternative Serialization of Simplicity DAGs>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-167><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|Bibliography>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-168><vspace|0.5fn>
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
  bit adder and full adder.

  <\render-code>
    <math|<math-ss|adder><rsub|1>\<of\><2>\<times\><2>\<vdash\><2><rsup|2>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|adder><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|cond>
    <around*|(|<math-ss|iden> \<vartriangle\> <math-ss|not> <math-ss|iden>|)>
    <around*|(|<math-ss|false> \<vartriangle\> <math-ss|iden>|)>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|full-adder><rsub|1>\<of\><around*|(|<2>\<times\><2>|)>\<times\><2>\<vdash\><2><rsup|2>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-adder><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|take>
    <math-ss|adder><rsub|1> \<vartriangle\>
    <math-ss|IH>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|OOH>
    \<vartriangle\> <around*|(|<math-ss|OIH> \<vartriangle\>
    <math-ss|IH>;<math-ss|adder><rsub|1>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|<math|<math-ss|cond>
    <math-ss|true> <math-ss|OH> \<vartriangle\> <math-ss|IIH>>>>>>>>>>>>>>
  </render-code>

  These adders meet the following specifications.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|adder><rsub|1>|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|2>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|1>+<around*|\<lceil\>|b|\<rceil\>><rsub|1>>>|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|1>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|2>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|1>+<around*|\<lceil\>|b|\<rceil\>><rsub|1>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>>>>
  </eqnarray*>

  It is easy to exhaustively check the above equations because there are only
  a small finite number of possible inputs to consider (four inputs for
  <math|<math-ss|adder><rsub|1>> and eight inputs for
  <math|<math-ss|full-adder><rsub|1>>). We will illustrate this for a single
  case for <math|<math-ss|adder><rsub|1>> where
  <math|a=<math-tt|1><rsub|<2>>> and <math|b=<math-tt|0><rsub|<2>>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|adder><rsub|1>|\<rrbracket\>><around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>|\<rceil\>><rsub|2>>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|cond>
    <around*|(|<math-ss|iden> \<vartriangle\> <math-ss|not> <math-ss|iden>|)>
    <around*|(|<math-ss|false> \<vartriangle\>
    <math-ss|iden>|)>|\<rrbracket\>><around*|\<langle\>|<math-tt|1><rsub|<2>>,<math-tt|0><rsub|<2>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|iden>
    \<vartriangle\> <math-ss|not> <math-ss|iden>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<around*|\<llbracket\>|<math-ss|iden>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>,<around*|\<llbracket\>|<math-ss|not>
    <math-ss|iden>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|0><rsub|<2>>,<around*|\<llbracket\>|<around*|(|<math-ss|pair>
    <math-ss|iden> <math-ss|unit>|)>;<around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|0><rsub|<2>>,<around*|\<llbracket\>|<around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>|\<rrbracket\>>\<circ\><around*|\<llbracket\>|<around*|(|<math-ss|pair>
    <math-ss|iden> <math-ss|unit>|)>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|0><rsub|<2>>,<around*|\<llbracket\>|<around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>|\<rrbracket\>><around*|\<langle\>|<around*|\<llbracket\>|<math-ss|iden>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>,<around*|\<llbracket\>|<math-ss|unit>|\<rrbracket\>><around*|(|<math-tt|0><rsub|<2>>|)>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|0><rsub|<2>>,<around*|\<llbracket\>|<around*|(|<math-ss|cond>
    <math-ss|false> <math-ss|true>|)>|\<rrbracket\>><around*|\<langle\>|<math-tt|0><rsub|<2>>,<around*|\<langle\>||\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|0><rsub|<2>>,<around*|\<llbracket\>|<math-ss|true>|\<rrbracket\>><around*|\<langle\>||\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|<math-tt|0><rsub|<2>>,1<rsub|<2>>|\<rangle\>>|\<rceil\>><rsub|2>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<math-tt|0><rsub|<2>>|\<rceil\>><rsub|1>\<cdot\>2<rsup|1>+<around*|\<lceil\>|<math-tt|1><rsub|<2>>|\<rceil\>><rsub|1>>>|<row|<cell|>|<cell|=>|<cell|0\<cdot\>2+1>>|<row|<cell|>|<cell|=>|<cell|1>>|<row|<cell|>|<cell|=>|<cell|1+0>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|<math-tt|1><rsub|<2>>|\<rceil\>><rsub|1>+<around*|\<lceil\>|<math-tt|0><rsub|<2>>|\<rceil\>><rsub|1>>>>>
  </eqnarray*>

  The calculations for the other cases are similar.

  Next, we recursively build adders and full adders for any word size.

  <\render-code>
    <math|<math-ss|full-adder><rsub|2*n>\<of\><around*|(|<2><rsup|2*n>\<times\><2><rsup|2*n>|)>\<times\><2>\<vdash\><2>\<times\><2><rsup|2*n>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-adder><rsub|2*n>>>|<cell|:=>|<cell|<math|<math-ss|take>
    <around*|(|<math-ss|OOH> \<vartriangle\> <math-ss|IOH>|)> \<vartriangle\>
    <around*|(|<math-ss|take> <around*|(|<math-ss|OIH> \<vartriangle\>
    <math-ss|IIH>|)> \<vartriangle\> <math-ss|IH>;<math-ss|full-adder><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IIH>
    \<vartriangle\> <around*|(|<math-ss|OH> \<vartriangle\>
    <math-ss|IOH>;<math-ss|full-adder><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IOH>
    \<vartriangle\> <around*|(|<math-ss|IIH> \<vartriangle\>
    <math-ss|OH>|)>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|adder><rsub|2*n>\<of\><2><rsup|2*n>\<times\><2><rsup|2*n>\<vdash\><2>\<times\><2><rsup|2*n>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|adder><rsub|2*n>>>|<cell|:=>|<cell|<math|<around*|(|<math-ss|OOH>
    \<vartriangle\> <math-ss|IOH>|)> \<vartriangle\> <around*|(|<math-ss|OIH>
    \<vartriangle\> <math-ss|IIH>;<math-ss|adder><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IIH>
    \<vartriangle\> <around*|(|<math-ss|OH> \<vartriangle\>
    <math-ss|IOH>;<math-ss|full-adder><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|IOH>
    \<vartriangle\> <around*|(|<math-ss|IIH> \<vartriangle\>
    <math-ss|OH>|)>>>>>>>>>>>>
  </render-code>

  We generalize the specification of the single bit adders and full adders to
  the multi-bit adders and full adders.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|1,n>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|n>+<around*|\<lceil\>|b|\<rceil\>><rsub|n>>>|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|1,n>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|n>+<around*|\<lceil\>|b|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>>>>
  </eqnarray*>

  <\theorem>
    For all <math|n> which is a power of 2, and for all <math|a:<2><rsup|n>>,
    <math|b:<2><rsup|n>>, and <math|c:<2>>, we have that
    <math|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|1,n>=<around*|\<lceil\>|a|\<rceil\>><rsub|n>+<around*|\<lceil\>|b|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>.
  </theorem>

  <\proof>
    We prove <math|<math-ss|full-adder><rsub|n>> meets its specification by
    induction on <math|n>. As mentioned before, the
    <math|<math-ss|full-adder><rsub|1>> case is easily checked by verifying
    all eight possible inputs. Next, we prove that
    <math|<math-ss|full-adder><rsub|2*n>> meets its specification under the
    assumption that <math|<math-ss|full-adder><rsub|n>> does. Specifically we
    need to show that

    <\equation>
      <around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|2*n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>,<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|1,2*n>=<around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1><label|full-adder-spec>
    </equation>

    Let us first consider the right hand side of equation
    <reference|full-adder-spec>. By the definition of our value function we
    have that

    <\eqnarray*>
      <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>|<cell|=>|<cell|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|a<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|b<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|a<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>>>>
    </eqnarray*>

    By our inductive hypothesis, we have that

    <\equation*>
      <around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|2>,b<rsub|2>|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|1,n>=<around*|\<lceil\>|a<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|2>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>
    </equation*>

    so we know that

    <\equation*>
      <around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>=<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|2>,b<rsub|2>|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|1,n>
    </equation*>

    Let us define <math|c<rsub|0>> and <math|r<rsub|0>> such that
    <math|<around*|\<langle\>|c<rsub|0>,r<rsub|0>|\<rangle\>>\<assign\><around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|2>,b<rsub|2>|\<rangle\>>,c|\<rangle\>>>.
    Thus we have that

    <\eqnarray*>
      <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|<around*|\<langle\>|c<rsub|0>,r<rsub|0>|\<rangle\>>|\<rceil\>><rsub|1,n>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|c<rsub|0>|\<rceil\>><rsub|1>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|0>|\<rceil\>><rsub|n>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c<rsub|0>|\<rceil\>><rsub|1>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|0>|\<rceil\>><rsub|n>>>>>
    </eqnarray*>

    Again, by our inductive hypothesis, we have that

    <\equation*>
      <around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,c<rsub|0>|\<rangle\>>|\<rceil\>><rsub|1,n>=<around*|\<lceil\>|a<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|b<rsub|1>|\<rceil\>><rsub|n>+<around*|\<lceil\>|c<rsub|0>|\<rceil\>><rsub|1>
    </equation*>

    therefore we have that

    <\equation*>
      <around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>=<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,c<rsub|0>|\<rangle\>>|\<rceil\>><rsub|1,n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|2>|\<rceil\>><rsub|n>
    </equation*>

    Let us define <math|c<rsub|1>> and <math|r<rsub|1>> such that
    <math|<around*|\<langle\>|c<rsub|1>,r<rsub|1>|\<rangle\>>\<assign\><around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,c<rsub|0>|\<rangle\>>>.
    Thus we have that

    <\eqnarray*>
      <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rceil\>><rsub|2*n>+<around*|\<lceil\>|c|\<rceil\>><rsub|1>>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|c<rsub|1>,r<rsub|1>|\<rangle\>>|\<rceil\>><rsub|1,n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|0>|\<rceil\>><rsub|n>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|1>|\<rceil\>><rsub|n>|)>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|0>|\<rceil\>><rsub|n>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>\<cdot\>2<rsup|2*n>+<around*|\<lceil\>|r<rsub|1>|\<rceil\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|0>|\<rceil\>><rsub|n><eq-number><label|full-adder-RHS>>>>>
    </eqnarray*>

    Now let us consider the left hand side of equation
    <reference|full-adder-spec>. By the definition and semantics of
    <math|<math-ss|full-adder><rsub|2*n>> we have that

    <\eqnarray*>
      <tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|full-adder><rsub|2*n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>,<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rangle\>>,c|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>
      \<vartriangle\> <around*|(|<math-ss|IIH> \<vartriangle\>
      <math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|\<circ\>>|<cell|<around*|\<llbracket\>|<math-ss|IIH>
      \<vartriangle\> <around*|(|<math-ss|OH> \<vartriangle\>
      <math-ss|IOH>;<math-ss|full-adder><rsub|n>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|\<circ\>>|<cell|<around*|\<llbracket\>|<math-ss|take>
      <around*|(|<math-ss|OOH> \<vartriangle\> <math-ss|IOH>|)>
      \<vartriangle\> <around*|(|<math-ss|take> <around*|(|<math-ss|OIH>
      \<vartriangle\> <math-ss|IIH>|)> \<vartriangle\>
      <math-ss|IH>;<math-ss|full-adder><rsub|n>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>,<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rangle\>>,c|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>
      \<vartriangle\> <around*|(|<math-ss|IIH> \<vartriangle\>
      <math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|\<circ\>>|<cell|<around*|\<llbracket\>|<math-ss|IIH>
      \<vartriangle\> <around*|(|<math-ss|OH> \<vartriangle\>
      <math-ss|IOH>;<math-ss|full-adder><rsub|n>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|2>,b<rsub|2>|\<rangle\>>,c|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>
      \<vartriangle\> <around*|(|<math-ss|IIH> \<vartriangle\>
      <math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|\<circ\>>|<cell|<around*|\<llbracket\>|<math-ss|IIH>
      \<vartriangle\> <around*|(|<math-ss|OH> \<vartriangle\>
      <math-ss|IOH>;<math-ss|full-adder><rsub|n>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,<around*|\<langle\>|c<rsub|0>,r<rsub|0>|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>
      \<vartriangle\> <around*|(|<math-ss|IIH> \<vartriangle\>
      <math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|r<rsub|0>,<around*|\<llbracket\>|<math-ss|full-adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,b<rsub|1>|\<rangle\>>,c<rsub|0>|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<llbracket\>|<math-ss|IOH>
      \<vartriangle\> <around*|(|<math-ss|IIH> \<vartriangle\>
      <math-ss|OH>|)>|\<rrbracket\>>>>|<row|<cell|>|<cell|>|<cell|<around*|\<langle\>|r<rsub|0>,<around*|\<langle\>|c<rsub|1>,r<rsub|1>|\<rangle\>>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<langle\>|c<rsub|1>,<around*|\<langle\>|r<rsub|1>,r<rsub|0>|\<rangle\>>|\<rangle\>>>>>>
    </eqnarray*>

    Therefore we have that

    <\eqnarray*>
      <tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-adder><rsub|2*n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,a<rsub|2>|\<rangle\>>,<around*|\<langle\>|b<rsub|1>,b<rsub|2>|\<rangle\>>|\<rangle\>>,c|\<rangle\>>|\<rceil\>><rsub|1,2*n>>|<cell|=>|<cell|<around*|\<lceil\>|<around*|\<langle\>|c<rsub|1>,<around*|\<langle\>|r<rsub|1>,r<rsub|0>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|1,2*n>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>\<cdot\>2<rsup|2*n>+<around*|\<lceil\>|<around*|\<langle\>|r<rsub|1>,r<rsub|0>|\<rangle\>>|\<rceil\>><rsub|2*n>>>|<row|<cell|>|<cell|=>|<cell|<around*|\<lceil\>|c<rsub|1>|\<rceil\>><rsub|1>\<cdot\>2<rsup|2*n>+<around*|\<lceil\>|r<rsub|1>|\<rceil\>><rsub|n>\<cdot\>2<rsup|n>+<around*|\<lceil\>|r<rsub|0>|\<rceil\>><rsub|n><eq-number><label|full-adder-LHS>>>>>
    </eqnarray*>

    Together equations <reference|full-adder-RHS> and
    <reference|full-adder-LHS> show that the right hand side and left hand
    side of equation <reference|full-adder-spec> are equal, as required.
  </proof>

  The proof that <math|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|adder><rsub|n>|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|1,n>=<around*|\<lceil\>|a|\<rceil\>><rsub|n>+<around*|\<lceil\>|b|\<rceil\>><rsub|n>>
  is done in a similar manner. Computer verified versions of theses proofs
  can be found in the Coq library (see Section<nbsp><reference|ss:coqArith>).

  With a full adder we can recursively build multipliers and full multiplier.

  <\render-code>
    <math|<math-ss|full-multiplier><rsub|1>\<of\><around*|(|<2>\<times\><2>|)>\<times\><around*|(|<2>\<times\><2>|)>\<vdash\><2><rsup|2>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-multiplier><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|IH>
    \<vartriangle\> <math-ss|take> <around*|(|<math-ss|cond> <math-ss|iden>
    <math-ss|false>|)>;<math-ss|full-adder><rsub|1>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|full-multiplier><rsub|2*n>\<of\><around*|(|<2><rsup|2*n>\<times\><2><rsup|2*n>|)>\<times\><around*|(|<2><rsup|2*n>\<times\><2><rsup|2*n>|)>\<vdash\><2><rsup|4*n>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|full-multiplier><rsub|2*n>>>|<cell|:=>|<cell|<math|<math-ss|take>
    <around*|(|<math-ss|OOH> \<vartriangle\> <around*|(|<math-ss|IOH>
    \<vartriangle\> <math-ss|OIH>|)>|)>>>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|(<math|<around*|(|<math-ss|take>
    <around*|(|<math-ss|OOH> \<vartriangle\> <math-ss|IIH>|)> \<vartriangle\>
    <math-ss|drop> <around*|(|<math-ss|OOH> \<vartriangle\>
    <math-ss|IOH>|)>;<math-ss|full-multiplier><rsub|n>|)>>>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|<math|<around*|(|<math-ss|take>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IIH>|)> \<vartriangle\>
    <math-ss|drop> <around*|(|<math-ss|OIH> \<vartriangle\>
    <math-ss|IOH>|)>;<math-ss|full-multiplier><rsub|n>|)>>)>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|take>
    <around*|(|<math-ss|OH> \<vartriangle\>
    <math-ss|IOH>|)>>>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|<math|<around*|(|<math-ss|drop>
    <around*|(|<math-ss|OOH> \<vartriangle\> <math-ss|IIH>|)> \<vartriangle\>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|drop>
    <around*|(|<math-ss|OIH> \<vartriangle\>
    <math-ss|IOH>|)>;<math-ss|full-multiplier><rsub|n>|)>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<around*|(|<math-ss|OH>
    \<vartriangle\> <math-ss|drop> <around*|(|<math-ss|IOH> \<vartriangle\>
    <math-ss|OOH>|)>;<math-ss|full-multiplier><rsub|n>|)> \<vartriangle\>
    <math-ss|drop> <around*|(|<math-ss|IIH> \<vartriangle\>
    <math-ss|OIH>|)>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|multiplier><rsub|1>\<of\><2>\<times\><2>\<vdash\><2><rsup|2>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|multiplier><rsub|1>>>|<cell|:=>|<cell|<math|<math-ss|false>
    \<vartriangle\> <math-ss|cond> <math-ss|iden> <math-ss|false>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|multiplier><rsub|2*n>\<of\><2><rsup|2*n>\<times\><2><rsup|2*n>\<vdash\><2><rsup|4*n>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|3|5|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|multiplier><rsub|2*n>>>|<cell|:=>|<cell|<math|<around*|(|<math-ss|OOH>
    \<vartriangle\> <around*|(|<math-ss|IOH> \<vartriangle\>
    <math-ss|OIH>|)>|)>>>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|<math|<around*|(|<math-ss|><around*|(|<math-ss|OOH>
    \<vartriangle\> <math-ss|IIH>|)>;<math-ss|multiplier><rsub|n>|)>
    \<vartriangle\> <around*|(|<around*|(|<math-ss|OIH> \<vartriangle\>
    <math-ss|IIH>|)>;<math-ss|multiplier><rsub|n>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<math-ss|take>
    <around*|(|<math-ss|OH> \<vartriangle\>
    <math-ss|IOH>|)>>>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|<math|<around*|(|<math-ss|drop>
    <around*|(|<math-ss|OOH> \<vartriangle\> <math-ss|IIH>|)> \<vartriangle\>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|drop>
    <around*|(|<math-ss|OIH> \<vartriangle\>
    <math-ss|IOH>|)>;<math-ss|full-multiplier><rsub|n>|)>|)>>>>|<row|<cell|>|<cell|;>|<cell|<math|<around*|(|<math-ss|OH>
    \<vartriangle\> <math-ss|drop> <around*|(|<math-ss|IOH> \<vartriangle\>
    <math-ss|OOH>|)>;<math-ss|full-multiplier><rsub|n>|)> \<vartriangle\>
    <math-ss|drop> <around*|(|<math-ss|IIH> \<vartriangle\>
    <math-ss|OIH>|)>>>>>>>>>>>>
  </render-code>

  We can prove that the multipliers and full multipliers meet the following
  specifications.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|full-multiplier><rsub|n>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a,b|\<rangle\>>,<around*|\<langle\>|c,d|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|2*n>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|n>\<cdot\><around*|\<lceil\>|b|\<rceil\>><rsub|n>+<around*|\<lceil\>|c|\<rceil\>><rsub|n>+<around*|\<lceil\>|d|\<rceil\>><rsub|n>>>|<row|<cell|<around*|\<lceil\>|<around*|\<llbracket\>|<math-ss|multiplier><rsub|n>|\<rrbracket\>><around*|\<langle\>|a,b|\<rangle\>>|\<rceil\>><rsub|2*n>>|<cell|=>|<cell|<around*|\<lceil\>|a|\<rceil\>><rsub|n>\<cdot\><around*|\<lceil\>|b|\<rceil\>><rsub|n>>>>>
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
  <math|SHA256<rsub|MD>\<of\><2><rsup|256>\<rightarrow\><around*|(|<2><rsup|512>|)><rsup|\<ast\>>\<rightarrow\><2><rsup|256>>.

  <\equation*>
    SHA256<rsub|<2>>=SHA256<rsub|MD><around*|(|SHA256<rsub|IV>|)>\<circ\>\<eta\><rsup|S>\<circ\>SHA256<rsub|Pad>
  </equation*>

  where <math|SHA256<rsub|IV>\<of\><2><rsup|256>> is the SHA-256 initial
  value and <math|\<eta\><rsup|S><rsub|A<rsup|+>>\<of\>A<rsup|+>\<rightarrow\>A<rsup|\<ast\>>>
  formally converts a non-empty list to a regular list.

  The <math|SHA256<rsub|MD>> function is a left fold using the SHA-256 block
  compression function <math|SHA256<rsub|Block>\<of\><2><rsup|256>\<times\><2><rsup|512>\<rightarrow\><2><rsup|256>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|SHA256<rsub|MD><around*|(|h|)><around*|(|\<epsilon\>|)>>|<cell|\<assign\>>|<cell|h>>|<row|<cell|SHA256<rsub|MD><around*|(|h|)><around*|\<langle\>|b\<blacktriangleleft\>l|\<rangle\>>>|<cell|\<assign\>>|<cell|SHA256<rsub|MD><around*|(|SHA256<rsub|Block><around*|\<langle\>|h,b|\<rangle\>>|)><around*|(|l|)>>>>>
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
  for the representation for field elements, of which the <verbatim|10x26>
  representation is the most portable. This representation consists of an
  array of 10 32-bit unsigned integer values. Such an array, <verbatim|a>,
  represents the value

  <\equation*>
    <big|sum><rsub|i=0><rsup|9><text|<verbatim|a[<math|i>]>>\<cdot\>2<rsup|26*i>
    <around*|(|mod p|)><text|.>
  </equation*>

  Different arrays may represent the same value. The various field arithmetic
  operations, including modular inverse and square roots, are implemented
  efficiently, subject to various specific preconditions on their inputs that
  need to be satisfied to prevent overflows of the internal 32-bit unsigned
  integer values.

  The libsecp256k1 library also has two variants for the representation of
  elliptic curve point values. The affine coordinate representation consists
  of a pair of field elements, and a flag to indicate the value
  <math|\<cal-O\>> (in which case the coordinate values are ignored). The
  Jacobian coordinate representation consists of a triple of field elements,
  and a flag to indicate the value <math|\<cal-O\>> (in which case the
  coordinates are ignored).

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
    FE\<assign\><2><rsup|32>\<times\><around*|(|<2><rsup|32>\<times\><around*|(|<2><rsup|32>\<times\><around*|(|<2><rsup|32>\<times\><around*|(|<2><rsup|32>\<times\><around*|(|<2><rsup|32>\<times\><around*|(|<2><rsup|32>\<times\><around*|(|<2><rsup|32>\<times\><around*|(|<2><rsup|32>\<times\><2><rsup|32>|)>|)>|)>|)>|)>|)>|)>|)>
  </equation*>

  and a value <math|<around*|\<langle\>|a<rsub|0>,<around*|\<langle\>|a<rsub|1>,<around*|\<langle\>|a<rsub|2>,<around*|\<langle\>|a<rsub|3>,<around*|\<langle\>|a<rsub|4>,<around*|\<langle\>|a<rsub|5>,<around*|\<langle\>|a<rsub|6>,<around*|\<langle\>|a<rsub|7>,<around*|\<langle\>|a<rsub|8>,a<rsub|9>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>\<of\>FE>
  represents the field element

  <\equation*>
    <around*|\<lceil\>|<around*|\<langle\>|a<rsub|0>,<around*|\<langle\>|a<rsub|1>,<around*|\<langle\>|a<rsub|2>,<around*|\<langle\>|a<rsub|3>,<around*|\<langle\>|a<rsub|4>,<around*|\<langle\>|a<rsub|5>,<around*|\<langle\>|a<rsub|6>,<around*|\<langle\>|a<rsub|7>,<around*|\<langle\>|a<rsub|8>,a<rsub|9>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rceil\>><rsub|FE>\<assign\><big|sum><rsup|9><rsub|i=0><around*|\<lceil\>|a<rsub|i>|\<rceil\>><rsub|32>\<cdot\>2<rsup|26*i>
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

  The translation between the libsecp256k1's <verbatim|10x32> field
  representation and Simplicity's <math|FE> type is straightforward. The
  translation between libsecp256k1's affine coordinate representation of
  elliptic curve points and Simplicity's <math|GE> is also straightforward
  except that Simplicity's <math|GE> type has no flag and cannot represent
  the <math|\<cal-O\>> point. The translation between libsecp256k1's Jacobian
  coordinate representation of elliptic curve points and Simplicity's
  <math|GEJ> type is mostly straight forward, however the <math|GEJ> type
  represents the <math|\<cal-O\>> point using a z-coordinate representing 0,
  while libsecp256k1 uses a flag to represent the <math|\<cal-O\>> point.

  The Simplicity implementation of libsecp256k1 is designed so that
  libsecp256k1 can be used as jets for these Simplicity expressions. As such,
  the Simplicity expressions are designed to mimic the exact behaviour of a
  specific version of libsecp256k1's elliptic curve functions. For inputs of
  particular representations of field elements, or points, the Simplicity
  expression returns the exact same representative for its result as
  libsecp256k1. If a precondition of a libsecp256k1 function is violated, the
  the Simplicity code also overflows and returns the corresponding value that
  libsecp256k1 returns. If an off-curve point is passed to a libsecp256k1
  function, the Simplicity code again computes the same result that the
  libsecp256k1 function does.

  The only subtle point with using libsecp256k1 for jets lies in the
  different representation of <math|\<cal-O\>>. The inputs and outputs of
  operations need to be suitable translated between the two representations.
  However, this can be done as part of the marshalling code for the jets, and
  the Simplicity expressions are written with this in mind.

  <subsubsection|Schnorr Signature Validation>

  With elliptic curve operations defined, we are able to implement Schnorr
  signature validation in accordance with the BIP-Schnorr
  specification<nbsp><cite|bip-schnorr>. We define Simplicity types for the
  formats of compressed public keys, <math|PubKey>; messages, <math|Msg>; and
  Schnorr signatures, <math|Sig>, below.

  <\eqnarray*>
    <tformat|<table|<row|<cell|PubKey>|<cell|\<assign\>>|<cell|<2>\<times\><2><rsup|256>>>|<row|<cell|Msg>|<cell|\<assign\>>|<cell|<2><rsup|256>>>|<row|<cell|Sig>|<cell|\<assign\>>|<cell|<2><rsup|512>>>>>
  </eqnarray*>

  The <math|PubKey> type is a pair <math|<around*|\<langle\>|b,<around*|\<lfloor\>|x|\<rfloor\>><rsub|256>|\<rangle\>>>
  where <math|b> is the least significant bit of a (non-<math|\<cal-O\>>)
  elliptic curve point's y-coordinate, and where <math|x> the point's
  x-coordinate. A <math|Msg> value <math|m> represents the byte-string
  <math|BE<rsub|256><around*|(|m|)>> for a Schnorr signature's message, and a
  <math|Sig> value <math|a> represents the byte-string
  <math|BE<rsub|512><around*|(|a|)>> for a Schnorr signature.

  We have implemented a core Simplicity expression to check a Schnorr
  signature for a public key on a given message:

  <\equation*>
    <math-ss|schnorrVerify>\<of\><around*|(|PubKey\<times\>Msg|)>\<times\>Sig\<vdash\><2>
  </equation*>

  The semantics are such that <math|<around*|\<llbracket\>|<math-ss|schnorrVerify>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|p,m|\<rangle\>>,s|\<rangle\>>=<math-tt|1><rsub|<2>>>
  only when the values that the inputs represents satisfy the verification
  conditions of the BIP-Schnorr specification.

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

  In modern Bitcoin, users who use P2SH (pay to script hash) do not commit
  funds directly to Bitcoin Script, rather they commit to a hash of their
  Bitcoin Script. Only when they wish to redeem their funds do they reveal
  their Bitcoin Script for execution. Bitcoin's consensus protocol enforces
  that the Bitcoin Script presented during redemption has a hash that matches
  the committed hash.

  <assign|cmr|<macro|x|<math|#<rsup|c><around*|(|<arg|x>|)>>>>Simplicity is
  designed to work in the same way. However, instead of a linear hash of a
  serialized Simplicity program (Section<nbsp><reference|Serialization>) we
  follow the tree structure of a Simplicity expression and compute a
  commitment Merkle root of its syntax tree. Below we define the commitment
  Merkle root of a Simplicity expression <math|t\<of\>A\<vdash\>B> as
  <math|<cmr|t>\<of\><2><rsup|256>>.

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<cmr|<math-ss|iden><rsub|A>>>|<cell|\<assign\>>|<cell|tag<rsup|c><rsub|<math-ss|iden>>>>|<row|<cell|<cmr|<math-ss|comp><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|comp>>\<comma\>
    <around*|\<langle\>|<cmr|s>,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|unit><rsub|A>>>|<cell|\<assign\>>|<cell|tag<rsup|c><rsub|<math-ss|unit>>>>|<row|<cell|<cmr|<math-ss|injl><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|injl>>\<comma\>
    <around*|\<langle\>|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|injr><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|injr>>\<comma\>
    <around*|\<langle\>|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|case><rsub|A,B,C,D>
    s t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|case>>\<comma\>
    <around*|\<langle\>|<cmr|s>,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|pair><rsub|A,B,C>
    s t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|pair>>\<comma\>
    <around*|\<langle\>|<cmr|s>,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|take><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|take>>\<comma\>
    <around*|\<langle\>|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|drop><rsub|A,B,C>
    t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|drop>>\<comma\>
    <around*|\<langle\>|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>,<cmr|t>|\<rangle\>>|\<rangle\>>>>>>
  </eqnarray*>

  Here we are directly using SHA-256's compression function,
  <math|SHA256*Block<around*|\<langle\>|i,b|\<rangle\>>>, which takes two
  arguments. The first argument, <math|i>, is a 256-bit initial value. The
  second value, <math|b>, is a 512-bit block of data. Above we divide a block
  into two 256-bit values, <math|<around*|\<langle\>|b<rsub|0>,b<rsub|1>|\<rangle\>>>,
  and recursively pass Merkle roots into the compression function.

  Like static analysis, the time needed to computing the commitment Merkle
  root is linear in the size of the DAG representing the term because the
  intermediate results on sub-expressions can be shared.

  We define unique initial values <math|tag<rsup|c><rsub|x>> for every
  combinator by taking the SHA-256 hash of unique byte strings:

  <\eqnarray*>
    <tformat|<table|<row|<cell|tag<rsup|c><rsub|<math-ss|iden>>>|<cell|\<assign\>>|<cell|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f6964656e]>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|comp>>>|<cell|\<assign\>>|<cell|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f636f6d70]>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|unit>>>|<cell|\<assign\>>|<cell|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f756e6974]>>>|<row|<cell|tag<rsup|c><rsub|<math-ss|injl>>>|<cell|\<assign\>>|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f696e6a6c]>>|<row|<cell|tag<rsup|c><rsub|<math-ss|injr>>>|<cell|\<assign\>>|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f696e6a72]>>|<row|<cell|tag<rsup|c><rsub|<math-ss|case>>>|<cell|\<assign\>>|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f63617365]>>|<row|<cell|tag<rsup|c><rsub|<math-ss|pair>>>|<cell|\<assign\>>|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f70616972]>>|<row|<cell|tag<rsup|c><rsub|<math-ss|take>>>|<cell|\<assign\>>|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f74616b65]>>|<row|<cell|tag<rsup|c><rsub|<math-ss|drop>>>|<cell|\<assign\>>|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f64726f70]>>>>
  </eqnarray*>

  Notice that the type annotations for expressions are not included in the
  commitment Merkle root. We will rely on type inference to derive principle
  type annotations (see Section<nbsp><with|color|red|<reference|ss:typeInference>>).
  Later, we will make use of this flexibility when pruning unused branches
  from <samp|case> expressions (see Section<nbsp><reference|ss:pruning>).

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
    b>>|<cell|\<assign\>>|<cell|tag<rsup|c><rsub|<math-ss|witness>>>>>>
  </eqnarray*>

  where <math|tag<rsup|c><rsub|<math-ss|witness>>> value is derived as the
  SHA-256 hash of a unique value.

  <\eqnarray*>
    <tformat|<table|<row|<cell|tag<rsup|c><rsub|<math-ss|witness>>>|<cell|\<assign\>>|<cell|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f7769746e657373]>>>>>
  </eqnarray*>

  Notice that a <math|<samp|witness> b> expression does not commit to its
  parameter in the commitment root. This means that at redemption time a
  <samp|witness> expression's parameter, called a <dfn|witness value>, could
  be set to any value.

  Witness values play the same role as Bitcoin Script's input stack in its
  <verbatim|sigScript> or Segwit's <verbatim|witness>. They act as inputs to
  Simplicity programs. Rather than accepting arguments as inputs and passing
  them down to where they are needed, <samp|witness> expressions lets input
  data appear right where it is needed.

  <subsection|Elided Computation>

  <subsection|Witness Merkle Root>

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

  We extend the definition of commitment Merkle root to support the new
  assertion and <samp|fail> expressions

  \;

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|1|2|2|cell-halign|r>|<table|<row|<cell|<cmr|<math-ss|assertl><rsub|A,B,C,D>
    s h>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|case>>\<comma\>
    <around*|\<langle\>|<cmr|s>,h|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|assertr><rsub|A,B,C,D>
    h t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|case>>\<comma\>
    <around*|\<langle\>|h,<cmr|t>|\<rangle\>>|\<rangle\>>>>|<row|<cell|<cmr|<math-ss|fail><rsub|A,B>
    h>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|fail>>,h|\<rangle\>>>>>>
  </eqnarray*>

  where <math|tag<rsup|c><rsub|<math-ss|fail>>> value is derived as the
  SHA-256 hash of a unique value.

  <\eqnarray*>
    <tformat|<table|<row|<cell|tag<rsup|c><rsub|<math-ss|fail>>>|<cell|\<assign\>>|<cell|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f6661696c]>>>>>
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

  We extend the definition of the commitment Merkle root to support the new
  expressions by hashing new unique byte strings.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<cmr|<math-ss|version>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[76657273696f6e]>|)>>>|<row|<cell|<cmr|<math-ss|lockTime>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[6c6f636b54696d65]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputsHash>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[696e7075747348617368]>|)>>>|<row|<cell|<cmr|<math-ss|<math|outputsHash>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[6f75747075747348617368]>|)>>>|<row|<cell|<cmr|<math-ss|<math|numInputs>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[6e756d496e70757473]>|)>>>|<row|<cell|<cmr|<math-ss|<math|totalInputValue>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[746f74616c496e70757456616c7565]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentPrevOutpoint>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[63757272656e74507265764f7574706f696e74]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentValue>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[63757272656e7456616c7565]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentSequence>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[63757272656e7453657175656e6365]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentIndex>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[63757272656e74496e646578]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputPrevOutpoint>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[696e707574507265764f7574706f696e74]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputValue>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[696e70757456616c7565]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputSequence>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[696e70757453657175656e6365]>|)>>>|<row|<cell|<cmr|<math-ss|<math|numOutput>s>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[6e756d784f757470757473]>|)>>>|<row|<cell|<cmr|<math-ss|<math|totalOutputValue>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[746f74616c4f757470757456616c7565]>|)>>>|<row|<cell|<cmr|<math-ss|<math|outputValue>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[6f757470757456616c7565]>|)>>>|<row|<cell|<cmr|<math-ss|outputScriptHash>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[6f757470757453637269707448617368]>|)>>>|<row|<cell|<cmr|<math-ss|<math|scriptCMR>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|BCprefix\<cdummy\><math-tt|[736372697074434d52]>|)>>>>>
  </eqnarray*>

  where

  <\equation*>
    BCprefix\<assign\><math-tt|[53696d706c69636974791f5072696d69746976651f426974636f696e1f]>
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
  and all inputs must authorize the transaction if the transaction is valid.

  Let us look at a basic example of a Simplicity program that requires a
  single Schnorr signature.

  <subsection|Example: <math-ss|checkSigHashAll>>

  Using Simplicity with witnesses, assertions and Bitcoin, we are able to
  build an expression that use Schnorr signatures to authorize spending of
  funds. Using the assertion extension we are able to define a variant of
  <math|<math-ss|schnorrVerify>> called <math|<math-ss|schnorrAssert>>:

  <\equation*>
    <math-ss|schnorrAssert>\<assign\> <math-ss|assert>
    <math-ss|schnorrVerify>\<of\><around*|(|PubKey\<times\>Msg|)>\<times\>Sig\<vdash\><1>
  </equation*>

  such that

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|schnorrAssert>|\<rrbracket\>><rsup|<maybe>><around*|\<langle\>|<around*|\<langle\>|p,m|\<rangle\>>,s|\<rangle\>>=\<eta\><rsup|<maybe>><around*|\<langle\>||\<rangle\>>>|<cell|\<Leftrightarrow\>>|<cell|<around*|\<llbracket\>|<math-ss|schnorrVerify>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|p,m|\<rangle\>>,s|\<rangle\>>=<math-tt|1><rsub|<2>><text|.>>>>>
  </eqnarray*>

  Next, we use the Bitcoin transaction extension to build a
  <math|<math-ss|sigHashAll>> expression that computes a SHA-256 hash that
  commits to all of the current transaction data from the environment and
  which input is being signed for.

  <\render-code>
    <math|<math-ss|sigAll>\<of\><1>\<vdash\><2><rsup|512>\<times\><2><rsup|512>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|3|3|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|sigAll>>>|<cell|:=>|<cell|<around*|(|<math|<math-ss|<math|inputsHash>>
    \<vartriangle\> <math-ss|<math|outputsHash>>>|)>>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|<math|<around*|(|<around*|(|<around*|(|<samp|currentValue>
    \<vartriangle\> <around*|(|<samp|currentIndex> \<vartriangle\>
    <math-ss|lockTime>|)>|)> |\<nobracket\>>|\<nobracket\>>>>>|<row|<cell|>|<cell|<math|\<vartriangle\>>>|<cell|<math|<around*|\<nobracket\>|
    <around*|\<nobracket\>| <around*|(|<around*|(|<math-ss|version>
    \<vartriangle\> <math-ss|scribe><around*|(|<around*|\<lfloor\>|2<rsup|31>|\<rfloor\>><rsub|32>|)>|)>
    \<vartriangle\> <math-ss|scribe><around*|(|<around*|\<lfloor\>|0|\<rfloor\>><rsub|64>|)>|)>|)>
    \<vartriangle\> <math-ss|scribe><around*|(|<around*|\<lfloor\>|1184|\<rfloor\>><rsub|256>|)>|)>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|ivSigAll>\<of\><1>\<vdash\><2><rsup|256>>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|ivSigAll>>>|<cell|:=>|<cell|<math|<around*|(|<math-ss|scribe>\<circ\>SHA256|)><around*|(|<math-tt|[53696d706c69636974791f5369676e61747572651d]>\<cdummy\>BE<rsub|256><around*|(|<cmr|<math-ss|sigAll>>|)>|)>>>>>>>>>>>>
  </render-code>

  <\render-code>
    <math|<math-ss|sigHashAll>\<of\><1>\<vdash\>Msg>

    <tabular|<tformat|<table|<row|<cell|<subtable|<tformat|<cwith|1|-1|2|2|cell-halign|r>|<table|<row|<cell|<math|<math-ss|sigHashAll>>>|<cell|:=>|<cell|<math|><math|<math-ss|sigAll>;<around*|(|<math-ss|ivSigAll>
    \<vartriangle\> <math-ss|OH>;<math-ss|sha256-block>|)> \<vartriangle\>
    <math-ss|IH>;<math-ss|sha256-block>>>>>>>>>>>>
  </render-code>

  The <math-ss|sigAll> expression reads a total of 672 bits of data from the
  environment. The <math-ss|ivSigAll> adds one 512-bit block constant prefix
  to this, which totals 1184 bits of data. While it is not strictly
  necessary, we choose to explicitly append the SHA-256 padding for this
  length of data.

  Notice that in <math-ss|ivSigAll>, in addition hashing the transaction data
  itself, we also hash the semantics of the data by including the commitment
  Merkle root of the Simplicity expression that generates the data. This
  fulfills the same role that including Bitcoin's sighash flags in its signed
  data does.

  Finally, we combine everything together into a single Simplicity program.
  Given a public key in compressed format <math|p\<of\>PubKey> and a
  formatted Schnorr signature <math|s\<of\>Sig> we can create the Simplicity
  program <math|<math-ss|checkSigHashAll><around*|\<langle\>|p,s|\<rangle\>>\<of\><1>\<vdash\><1>>

  <\equation*>
    <math-ss|checkSigHashAll><around*|\<langle\>|p,s|\<rangle\>>\<assign\><around*|(|<math-ss|scribe><rsub|PubKey><around*|(|p|)>
    \<vartriangle\> <math-ss|sigHashAll>|)> \<vartriangle\>
    <math-ss|witness><rsub|Sig><around*|(|s|)>;<math-ss|schnorrAssert>
  </equation*>

  The <math-ss|witness> combinator ensures that the program's commitment
  Merkle root <math|<cmr|<math-ss|checkSigHashAll><around*|\<langle\>|p,s|\<rangle\>>>>
  is independent of the value of the signature <math|s>. This allows us to
  commit to this program without knowing the signature, and only providing
  the signature at redemption time. As with normal Bitcoin transactions, the
  signature is only valid in the context, <math|e\<of\>BCEnv>, of a
  particular input on a particular transaction during redemption because our
  program only executes successfully, i.e.
  <math|<around*|\<llbracket\>|<math-ss|checkSigHashAll><around*|\<langle\>|p,s|\<rangle\>>|\<rrbracket\>><rsup|<BC>><around*|\<langle\>||\<rangle\>><around*|(|e|)>=\<eta\><rsup|<maybe>><around*|\<langle\>||\<rangle\>>>,
  when provided a witness that is a valid signature on the transaction data
  and input number.

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
    <tabular*|<tformat|<cwith|2|2|1|1|cell-tborder|1pt>|<cwith|2|2|1|1|cell-hyphen|n>|<cwith|1|1|1|1|cell-width|>|<cwith|1|1|1|1|cell-hmode|auto>|<cwith|2|2|1|1|cell-col-span|1>|<table|<row|<cell|<subtable|<tformat|<cwith|1|1|2|2|cell-halign|c>|<cwith|1|1|1|1|cell-halign|c>|<table|<row|<cell|<math|s\<of\>A\<times\><2><rsup|256>\<vdash\>B\<times\>C>>|<cell|<math|t\<of\>C\<vdash\>D>>>>>>>>|<row|<cell|<math|<math-ss|disconnect><rsub|A,B,C,D>
    s t\<of\>A\<vdash\>B\<times\>D>>>>>>
  </with>

  \;

  Semantically, the <samp|disconnect> combinator behaves similar to the
  composition combinator, but where the commitment Merkle root of the
  expression <math|t> is passed as an argument to the expression <math|s>. We
  extend the formal semantics to the <samp|disconnect> combinator as follows.

  <\equation*>
    <around*|\<llbracket\>|<math-ss|disconnect><rsub|A,B,C,D> s
    t|\<rrbracket\>><rsup|\<cal-M\>><around*|(|a|)>\<assign\><around*|\<llbracket\>|s;<math-ss|take>
    <math-ss|iden> \<vartriangle\> <math-ss|drop>
    t|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a,<cmr|t>|\<rangle\>>
  </equation*>

  Like a <samp|witness> expression, the real significance comes from the form
  of its commitment Merkle root. We extend the definition of the commitment
  Merkle root as follows.

  <\eqnarray*>
    <tformat|<cwith|1|-1|2|2|cell-halign|r>|<cwith|1|1|2|2|cell-halign|r>|<table|<row|<cell|<cmr|<math-ss|disconnect><rsub|A,B,C,D>
    s t>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|disconnect>>\<comma\>
    <around*|\<langle\>|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>,<cmr|s>|\<rangle\>>|\<rangle\>>>>>>
  </eqnarray*>

  where the <math|tag<rsup|c><rsub|<math-ss|disconnect>>> value is derived as
  the SHA-256 hash of a unique value.

  <\eqnarray*>
    <tformat|<table|<row|<cell|tag<rsup|c><rsub|<math-ss|disconnect>>>|<cell|\<assign\>>|<cell|SHA256<math-tt|[53696d706c69636974791f436f6d6d69746d656e741f646973636f6e6e656374]>>>>>
  </eqnarray*>

  The commitment Merkle root only commits to the first argument, <math|s>, of
  a <math|<samp|disconnect> s t> expression. During redemption the second
  argument, <math|t>, can be freely set to any Simplicity expression. In
  order to place restrictions on what <math|t> is allowed, the commitment
  Merkle root of <math|t> is passed to <math|s> as an input. This way
  <math|s> is allowed to dynamically decide if <math|t> is an acceptable
  expression to be used here.

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
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\> <math-ss|OH>|)> k;
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
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\> <math-ss|OH>|)> k;
    <math|<math-ss|IH>>|)>> <math|<math-ss|OH>>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<injl|<around*|(|a<rsub|1>|)>>,h|\<rangle\>>>>|<row||<cell|=>|<cell|<around*|\<llbracket\>|<math|<math-ss|disconnect>
    <around*|(|<math-ss|assert> <around*|(|<math-ss|OIH> \<vartriangle\>
    <math-ss|IH> ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|OH>|)> k; <math|<math-ss|IH>>>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math|<math-ss|IH>>|\<rrbracket\>><rsup|\<cal-M\>>\<leftarrowtail\><around*|\<llbracket\>|<math|<math-ss|disconnect>
    <around*|(|<math-ss|assert> <around*|(|<math-ss|OIH> \<vartriangle\>
    <math-ss|IH> ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|OH>|)> k>|\<rrbracket\>><rsup|\<cal-M\>>|)><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math|<math-ss|IH>>|\<rrbracket\>><rsup|\<cal-M\>>\<leftarrowtail\><around*|\<llbracket\>|<math-ss|assert>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|OH>;<math-ss|take> <math-ss|iden> \<vartriangle\> <math-ss|drop>
    k|\<rrbracket\>><rsup|\<cal-M\>>|)><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>,<cmr|k>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math|<math-ss|IH>>|\<rrbracket\>><rsup|\<cal-M\>>\<leftarrowtail\><around*|\<llbracket\>|<math-ss|take>
    <math-ss|iden> \<vartriangle\> <math-ss|drop>
    k|\<rrbracket\>><rsup|\<cal-M\>>\<leftarrowtail\><around*|\<llbracket\>|<math-ss|assert>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|OH>|\<rrbracket\>><rsup|\<cal-M\>>|)><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>,<cmr|k>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math-ss|take>
    <math-ss|iden> \<vartriangle\> <math-ss|drop>
    k;<math-ss|IH>|\<rrbracket\>><rsup|\<cal-M\>>\<leftarrowtail\><around*|\<llbracket\>|<math-ss|assert>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|OH>|\<rrbracket\>><rsup|\<cal-M\>>|)><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>,<cmr|k>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|<around*|\<llbracket\>|<math-ss|drop>
    k|\<rrbracket\>><rsup|\<cal-M\>>\<leftarrowtail\><around*|\<llbracket\>|<math-ss|assert>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|OH>|\<rrbracket\>><rsup|\<cal-M\>>|)><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>,<cmr|k>|\<rangle\>>>>>>
  </eqnarray*>

  For the first part we have

  <\eqnarray*>
    <tformat|<table|<row|<cell|>|<cell|>|<cell|<around*|\<llbracket\>|<math-ss|assert>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|OH>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>,<cmr|k>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|\<iota\><rsup|\<cal-M\>><rsub|<maybe>><around*|(|<around*|\<llbracket\>|<math-ss|assert>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|OH>|\<rrbracket\>><rsup|<maybe>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>,<cmr|k>|\<rangle\>>|)>>>|<row|<cell|>|<cell|=>|<cell|\<iota\><rsup|\<cal-M\>><rsub|<maybe>><around*|(|\<phi\><rsup|<maybe>><around*|\<langle\>|<around*|\<llbracket\>|<math-ss|assert>
    <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IH>
    ;<math-ss|eq><rsub|<2><rsup|256>>|)>|\<rrbracket\>><rsup|<maybe>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>,<cmr|k>|\<rangle\>>,\<eta\><rsup|S><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>|)>>>|<row|<cell|>|<cell|=>|<cell|\<iota\><rsup|\<cal-M\>><rsub|<maybe>><around*|(|\<phi\><rsup|<maybe>><around*|\<langle\>|<around*|\<llbracket\>|<math-ss|OIH>
    \<vartriangle\> <math-ss|IH> ;<math-ss|eq><rsub|<2><rsup|256>>|\<rrbracket\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>,<cmr|k>|\<rangle\>>,\<eta\><rsup|S><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>|)>>>|<row|<cell|>|<cell|=>|<cell|\<iota\><rsup|\<cal-M\>><rsub|<maybe>><around*|(|\<phi\><rsup|<maybe>><around*|\<langle\>|<around*|\<llbracket\>|<math-ss|eq><rsub|<2><rsup|256>>|\<rrbracket\>><around*|\<langle\>|h,<cmr|k>|\<rangle\>>,\<eta\><rsup|S><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>|)>>>>>
  </eqnarray*>

  We know that <math|<around*|\<llbracket\>|<math-ss|eq><rsub|<2><rsup|256>>|\<rrbracket\>><around*|\<langle\>|h,<cmr|k>|\<rangle\>>=<math-tt|1><rsub|<2>>=\<eta\><rsup|S><around*|\<langle\>||\<rangle\>>>
  if and only if <math|h=<cmr|k>> and that
  <math|<around*|\<llbracket\>|<math-ss|eq><rsub|<2><rsup|256>>|\<rrbracket\>><around*|\<langle\>|h,<cmr|k>|\<rangle\>>=<math-tt|0><rsub|<2>>=\<emptyset\><rsup|S>>
  if and only if <math|h\<neq\><cmr|k>>. When <math|h\<neq\><cmr|k>>, then

  <\equation*>
    <around*|\<llbracket\>|<math-ss|assert> <around*|(|<math-ss|OIH>
    \<vartriangle\> <math-ss|IH> ;<math-ss|eq><rsub|<2><rsup|256>>|)>
    \<vartriangle\> <math-ss|OH>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>,<cmr|k>|\<rangle\>>=\<emptyset\><rsup|\<cal-M\>>
  </equation*>

  and the whole <samp|loopBody> expression fails with a
  <math|\<emptyset\><rsup|\<cal-M\>><rsub|B>> result. However, when
  <math|h=<cmr|k>> we have that

  <\equation*>
    <around*|\<llbracket\>|<math-ss|assert> <around*|(|<math-ss|OIH>
    \<vartriangle\> <math-ss|IH> ;<math-ss|eq><rsub|<2><rsup|256>>|)>
    \<vartriangle\> <math-ss|OH>|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>,<cmr|k>|\<rangle\>>=\<eta\><rsup|\<cal-M\>><around*|\<langle\>|<around*|\<langle\>||\<rangle\>>,<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>
  </equation*>

  and we can continue with

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|\<llbracket\>|<math-ss|drop>
    k|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|<around*|\<langle\>||\<rangle\>>,<around*|\<langle\>|a<rsub|1>,h|\<rangle\>>|\<rangle\>>>|<cell|=>|<cell|<around*|\<llbracket\>|k|\<rrbracket\>><rsup|\<cal-M\>><around*|\<langle\>|a<rsub|1>,h|\<rangle\>>>>>>
  </eqnarray*>

  and the result is that

  <\equation*>
    <around*|\<llbracket\>|<samp|case> <math|<around*|(|<math-ss|disconnect>
    <around*|(|<math-ss|assert> <around*|(|<math-ss|OIH> \<vartriangle\>
    <math-ss|IH> ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
    <math-ss|OH>|)> k; <math|<math-ss|IH>>|)>>
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
      <tformat|<table|<row|<cell|loopBodyCMR<around*|(|t|)>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|comp>>\<comma\>
      <around*|\<langle\>|<cmr|<math-ss|take> t \<vartriangle\>
      <math-ss|IH>>,SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|case>>\<comma\>
      <around*|\<langle\>|loopTail,<cmr|<math-ss|OH>>|\<rangle\>>|\<rangle\>>|\<rangle\>>|\<rangle\>>>>>>
    </eqnarray*>

    and

    <\eqnarray*>
      <tformat|<table|<row|<cell|loopTail>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|comp>>\<comma\>
      <around*|\<langle\>|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|disconnect>>\<comma\>
      <around*|\<langle\>|<around*|\<lfloor\>|0|\<rfloor\>><rsub|256>,<cmr|<math-ss|assert>
      <around*|(|<math-ss|OIH> \<vartriangle\> <math-ss|IH>
      ;<math-ss|eq><rsub|<2><rsup|256>>|)> \<vartriangle\>
      <math-ss|OH>>|\<rangle\>>|\<rangle\>>,<cmr|<math-ss|IH>>|\<rangle\>>|\<rangle\>><text|.>>>>>
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
      <tformat|<table|<row|<cell|loopCMR<around*|(|t|)>>|<cell|\<assign\>>|<cell|SHA256<rsub|Block><around*|\<langle\>|tag<rsup|c><rsub|<math-ss|comp>>\<comma\>
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

  <chapter|Type Inference and Serialization>

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
  Simplicity's consensus operations, from computing witness Merkle roots to
  evaluation of Simplicity expressions using the Bit Machine, can operate
  without flattening the representation of the inferred types.

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
  and the commitment Merkle root and witness Merkle roots for part of the
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
  a word has. The <verbatim|fromWord> and <verbatim|toWord> functions convert
  values of Simplicity words types to and from Haskell <verbatim|Integer>s
  (modulo the size of the word). The file also provides specializations of
  these various functions for popular word sizes between 1 and 512 bits.

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
  instances of Simplicity terms that compute the commitment and witness
  Merkle roots. The <verbatim|commitmentRoot> and <verbatim|witnessRoot>
  return these Merkle root values. The <verbatim|Simplicity/MerkleRoot.hs>
  module also provides a memoized computation of the Merkle roots for
  Simplicity types.

  The SHA-256 implementation is provided through an abstract interface found
  in <verbatim|Core/Simplicity/Digest.hs>, which in turn references an
  implementation of a 256-bit word type defined in
  <verbatim|Core/Simplicity/Word.hs>.

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
  multi-bit word expressions that operate on Simplicity's word types. It
  provides the standard implementations of the <verbatim|zero>,
  <verbatim|adder>, <verbatim|fullAdder>, <verbatim|subtractor>,
  <verbatim|fullSubtractor>, <verbatim|multiplier>, and
  <verbatim|fullMultiplier> Simplicity expressions. Notice that the
  implementation of these functions is careful to use explicit sharing of
  Simplicity sub-expressions through the <verbatim|where> clauses.

  The <verbatim|shift> and <verbatim|rotate> functions create Simplicity
  expressions that do right shifts and rotates of multi-bit words by any
  constant amount. Left (unsigned) shifts and rotates can be made by passing
  a negative value for the shift/rotate amount.

  The <verbatim|bitwise> combinator takes a Simplicity expression for a
  binary bit operation and lifts it to a Simplicity expression for a binary
  operation on arbitrary sized words that performs the bit operation
  bit-wise. There is also a variant, called <verbatim|bitwiseTri> the does
  the same thing for trinary bit operations.

  <subsubsection|Generic>

  The <verbatim|Core/Simplicity/Programs/Generic.hs> file provides some
  Simplicity expressions that can apply to any Simplicity type.

  The <verbatim|scribe> function produces a Simplicity expression denoting a
  constant function for any value for any Simplicity type. The <verbatim|eq>
  Simplicity expression compares any two values of the same Simplicity type
  and decides if they are equal or not.

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
  finite field with the <verbatim|10x26> limb representation, elliptic curve
  point operations in affine and Jacobian coordinates, and linear
  combinations of points.

  This module also include the <verbatim|schnorrVerify> and
  <verbatim|schnorrAssert> expressions that implement Schnorr signatures as
  specified in BIP-Schnorr<nbsp><cite|bip-schnorr>.

  The <verbatim|mkLib> function builds the library from the its dependency,
  the SHA-256 library. The <verbatim|lib> value illustrates how to build the
  library, but using the <verbatim|lib> value will not allow you to share the
  dependency, so it should only be used for testing purposed.

  The <verbatim|Core/Simplicity/Programs/LibSecp256k1/Lib.hs> file provides
  an unpacked module version of the library. However use of this module will
  lose the subexpression sharing. Therefore this should only be used for
  testing purposes.

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

  <subsection|<verbatim|JetType> class>

  While the <verbatim|Jet> class allows any expression to be a jet, in
  reality there we will have a specific set of known jets that we have
  accelerated implements of. The <verbatim|Indef/Simplicity/JetType.hs>
  defines the <verbatim|JetType> class whose instances are types which
  represent sets of known discounted jets. \ The <verbatim|specification>
  method define the specification of discounted jets and the
  <verbatim|matcher> method decides if a given Simplicity expression is known
  to be substitutable by a some discounted jet. There are also
  <verbatim|putJetBit> and <verbatim|getJetBit> used for Serialization (see
  Section<nbsp><reference|ss:Haskell-Serialization>)

  Because the set of discounted jets in use could vary over time, the
  <verbatim|JetType> class allows for different types to represent different
  sets of discounted jets. \ You can have a different <verbatim|JetType>
  instance for each version of the set of discounted jets.

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
  <verbatim|checkSigHashAll> Simplicity expression library that verifies
  Schnorr signature over the Bitcoin specific transaction data hash produced
  by <verbatim|sigHashAll> for a provided public key. Some variants of this
  expression are also provided including <verbatim|pkwCheckSigHashAll> which
  builds a complete Simplicity program from a given public key and signature.

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

    <item>Jets for elliptic curve functions, including Schnorr signature
    verification.
  </itemize>

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

  <\small>
    <\eqnarray*>
      <tformat|<table|<row|<cell|<cmr|<math-ss|version>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[76657273696f6e]>|)>>>|<row|<cell|<cmr|<math-ss|lockTime>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[6c6f636b54696d65]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputsHash>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[696e7075747348617368]>|)>>>|<row|<cell|<cmr|<math-ss|<math|outputsHash>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[6f75747075747348617368]>|)>>>|<row|<cell|<cmr|<math-ss|<math|numInputs>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[6e756d496e70757473]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputIsPegin>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[696e7075744973506567696e]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputPrevOutpoint>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[696e707574507265764f7574706f696e74]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputAsset>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[696e7075744173736574]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputAmount>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[696e707574416d6f756e74]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputScriptHash>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[696e70757453637269707448617368]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputSequence>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[696e70757453657175656e6365]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputIssuanceBlinding>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[696e70757449737375616e6365426c696e64696e67]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputIssuanceContract>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[696e70757449737375616e6365436f6e7472616374]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputIssuanceEntropy>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[696e70757449737375616e6365456e74726f7079]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputIssuanceAssetAmt>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[696e70757449737375616e63654173736574416d74]>|)>>>|<row|<cell|<cmr|<math-ss|<math|inputIssuanceTokenAmt>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[696e70757449737375616e6365546f6b656e416d74]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentIndex>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[63757272656e74496e646578]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentIsPegin>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[63757272656e744973506567696e]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentPrevOutpoint>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[63757272656e74507265764f7574706f696e74]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentAsset>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[63757272656e744173736574]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentAmount>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[63757272656e74416d6f756e74]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentScriptHash>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[63757272656e7453637269707448617368]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentSequence>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[63757272656e7453657175656e6365]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentIssuanceBlinding>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[63757272656e7449737375616e6365426c696e64696e67]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentIssuanceContract>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[63757272656e7449737375616e6365436f6e7472616374]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentIssuanceEntropy>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[63757272656e7449737375616e6365456e74726f7079]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentIssuanceAssetAmt>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[63757272656e7449737375616e63654173736574416d74]>|)>>>|<row|<cell|<cmr|<math-ss|<math|currentIssuanceTokenAmt>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[63757272656e7449737375616e6365546f6b656e416d74]>|)>>>|<row|<cell|<cmr|<math-ss|<math|numOutput>s>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[6e756d784f757470757473]>|)>>>|<row|<cell|<cmr|<math-ss|<math|outputAsset>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[6f75747075744173736574]>|)>>>|<row|<cell|<cmr|<math-ss|<math|outputAmount>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[6f7574707574416d6f756e74]>|)>>>|<row|<cell|<cmr|<math-ss|<math|outputNonce>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[6f75747075744e6f6e6365]>|)>>>|<row|<cell|<cmr|<math-ss|outputScriptHash>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[6f757470757453637269707448617368]>|)>>>|<row|<cell|<cmr|<math-ss|outputNullDatum>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[6f75747075744e756c6c446174756d]>|)>>>|<row|<cell|<cmr|<math-ss|fee>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[666565]>|)>>>|<row|<cell|<cmr|<math-ss|<math|scriptCMR>>>>|<cell|\<assign\>>|<cell|SHA256<around*|(|ELprefix\<cdummy\><math-tt|[736372697074434d52]>|)>>>>>
    </eqnarray*>
  </small>

  \;

  where

  <\equation*>
    ELprefix\<assign\><math-tt|[53696d706c69636974791f5072696d69746976651f456c656d6e74731f]>
  </equation*>

  <subsection|Serialization>

  Below we give codes for Elements primitive names. The prefix codes for
  primitive names all begin with <math|<verbatim|[10]><rsub|<2>>>.

  <\eqnarray*>
    <tformat|<table|<row|<cell|<rep|<text|<samp|`version'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10000000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`lockTime'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10000001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputIsPegin'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputPrevOutpoint'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000010|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputAsset'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000011|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputAmount'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10001000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputScriptHash'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10001001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputSequence'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000101|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputIssuanceBlinding'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000110|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputIssuanceContract'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1000111|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputIssuanceEntropy'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10010000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputIssuanceAssetAmt'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10010001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputIssuanceTokenAmt'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1001001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputAsset'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1001010|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputAmount'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1001011|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputNonce'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10011000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputScriptHash'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|10011001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputNullDatum'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1001101|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`scriptCMR'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1001110|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentIsPegin'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentPrevOutpoint'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentAsset'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010010|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentAmount'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010011|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentScriptHash'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010100|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentSequence'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010101|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentIssuanceBlinding'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010110|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentIssuanceContract'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1010111|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentIssuanceEntropy'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1011000|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentIssuanceAssetAmt'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1011001|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`currentIssuanceTokenAmt'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1011010|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`inputsHash'>>|>>|<cell|=>|<cell|<rsub|><verbatim|<around*|[|1011011|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`outputsHash'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1011100|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`numInputs'>>|>>|<cell|=>|<verbatim|<around*|[|1011101|]>><rsub|<2>>>|<row|<cell|<rep|<text|<samp|`numOutputs'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1011110|]>><rsub|<2>>>>|<row|<cell|<rep|<text|<samp|`fee'>>|>>|<cell|=>|<cell|<verbatim|<around*|[|1011111|]>><rsub|<2>>>>>>
  </eqnarray*>

  <section|Jets>

  <with|color|red|UNDER DEVELOPMENT>

  \;

  <math|<samp|inputIssuance>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<maybe><around*|(|<2>|)>|)>>

  <math|<samp|inputIssuanceAsset>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<maybe><around*|(|ExplicitAsset|)>|)>>

  <math|<samp|currentIssuance>\<of\><value|1>\<vdash\><maybe><around*|(|<2>|)>><with|color|red|Either
  an issuance or reissuance or neither>

  <math|<samp|currentIssuanceAsset>\<of\><value|1>\<vdash\><maybe><around*|(|ExplicitAsset|)>>

  <math|<samp|outputIsFee>\<of\><2><rsup|32>\<vdash\><maybe><around*|(|<2>|)>>

  \;

  Notes: use <samp|IssuanceContractHash> and <samp|IssuanceEntropy> to decide
  which issuance kind, if any, is being invoked.

  <with|color|red|We also want jets for computing AssetIDs and TokenIDs from
  entropy and probably also from contractHash.><appendix|Alternative
  Serialization of Simplicity DAGs><label|app:AltSerialization>

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

      <bibitem*|17><label|bib-bip-schnorr>P.<nbsp>Wuille.<newblock>
      Bip-schnorr.<newblock> 2018.<newblock>
      <slink|Https://github.com/sipa/bips/blob/bip-schnorr/bip-schnorr.mediawiki>.<newblock>

      <bibitem*|18><label|bib-libsecp256k1>P.<nbsp>Wuille.<newblock>
      Libsecp256k1.<newblock> <slink|https://github.com/bitcoin-core/secp256k1/tree/1e6f1f5ad5e7f1e3ef79313ec02023902bf8175c>,
      May 2018.<newblock>
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
    <associate|LC218|<tuple|6.2.2|?>>
    <associate|LC219|<tuple|<with|mode|<quote|math>|\<bullet\>>|?>>
    <associate|LC267|<tuple|6.1|?>>
    <associate|LC313|<tuple|6.5|?>>
    <associate|LC42|<tuple|6.5|?>>
    <associate|LC98|<tuple|6.2.2|?>>
    <associate|SS:Coq:MerkleRoots|<tuple|8.5|71>>
    <associate|Serialization|<tuple|2.8|?>>
    <associate|app:AltSerialization|<tuple|B|95>>
    <associate|app:ElementsTransactions|<tuple|A|87>>
    <associate|auto-1|<tuple|1|7>>
    <associate|auto-10|<tuple|2.2|13>>
    <associate|auto-100|<tuple|7.2.1|62>>
    <associate|auto-101|<tuple|7.2.2|63>>
    <associate|auto-102|<tuple|8|65>>
    <associate|auto-103|<tuple|8.1|65>>
    <associate|auto-104|<tuple|8.2|65>>
    <associate|auto-105|<tuple|8.2.1|65>>
    <associate|auto-106|<tuple|8.2.2|65>>
    <associate|auto-107|<tuple|8.2.2.1|66>>
    <associate|auto-108|<tuple|8.2.2.2|66>>
    <associate|auto-109|<tuple|8.2.2.3|67>>
    <associate|auto-11|<tuple|2.2.1|13>>
    <associate|auto-110|<tuple|8.2.3|67>>
    <associate|auto-111|<tuple|8.3|67>>
    <associate|auto-112|<tuple|8.3.1|67>>
    <associate|auto-113|<tuple|8.3.2|67>>
    <associate|auto-114|<tuple|8.3.3|68>>
    <associate|auto-115|<tuple|8.4|68>>
    <associate|auto-116|<tuple|8.1|68>>
    <associate|auto-117|<tuple|8.4.1|69>>
    <associate|auto-118|<tuple|8.4.2|69>>
    <associate|auto-119|<tuple|8.4.3|69>>
    <associate|auto-12|<tuple|2.2.2|13>>
    <associate|auto-120|<tuple|8.4.4|70>>
    <associate|auto-121|<tuple|8.4.4.1|70>>
    <associate|auto-122|<tuple|8.4.5|70>>
    <associate|auto-123|<tuple|8.4.6|71>>
    <associate|auto-124|<tuple|8.5|71>>
    <associate|auto-125|<tuple|8.6|71>>
    <associate|auto-126|<tuple|8.6.1|72>>
    <associate|auto-127|<tuple|8.6.1.1|72>>
    <associate|auto-128|<tuple|8.6.2|73>>
    <associate|auto-129|<tuple|8.6.3|73>>
    <associate|auto-13|<tuple|2.3|15>>
    <associate|auto-130|<tuple|9|75>>
    <associate|auto-131|<tuple|9.1|75>>
    <associate|auto-132|<tuple|9.1.1|75>>
    <associate|auto-133|<tuple|9.1.2|76>>
    <associate|auto-134|<tuple|9.1.3|77>>
    <associate|auto-135|<tuple|9.1.4|77>>
    <associate|auto-136|<tuple|9.1.5|77>>
    <associate|auto-137|<tuple|9.1.5.1|77>>
    <associate|auto-138|<tuple|9.1.5.2|77>>
    <associate|auto-139|<tuple|9.1.5.3|77>>
    <associate|auto-14|<tuple|2.3.1|15>>
    <associate|auto-140|<tuple|9.1.5.4|78>>
    <associate|auto-141|<tuple|9.1.6|78>>
    <associate|auto-142|<tuple|9.1.6.1|78>>
    <associate|auto-143|<tuple|9.1.6.2|78>>
    <associate|auto-144|<tuple|9.1.7|79>>
    <associate|auto-145|<tuple|9.1.7.1|79>>
    <associate|auto-146|<tuple|9.1.7.2|79>>
    <associate|auto-147|<tuple|9.2|80>>
    <associate|auto-148|<tuple|9.2.1|80>>
    <associate|auto-149|<tuple|9.2.2|80>>
    <associate|auto-15|<tuple|2.3.2|16>>
    <associate|auto-150|<tuple|9.2.3|80>>
    <associate|auto-151|<tuple|9.2.4|81>>
    <associate|auto-152|<tuple|9.2.5|81>>
    <associate|auto-153|<tuple|9.2.6|81>>
    <associate|auto-154|<tuple|9.2.6.1|82>>
    <associate|auto-155|<tuple|9.2.6.2|83>>
    <associate|auto-156|<tuple|9.3|83>>
    <associate|auto-157|<tuple|9.4|84>>
    <associate|auto-158|<tuple|9.4.1|84>>
    <associate|auto-159|<tuple|9.4.2|84>>
    <associate|auto-16|<tuple|2.3.3|16>>
    <associate|auto-160|<tuple|9.5|85>>
    <associate|auto-161|<tuple|10|87>>
    <associate|auto-162|<tuple|A|89>>
    <associate|auto-163|<tuple|A.1|92>>
    <associate|auto-164|<tuple|A.1.1|93>>
    <associate|auto-165|<tuple|A.1.2|93>>
    <associate|auto-166|<tuple|A.1.3|94>>
    <associate|auto-167|<tuple|A.2|95>>
    <associate|auto-168|<tuple|B|97>>
    <associate|auto-169|<tuple|B|?>>
    <associate|auto-17|<tuple|2.3.4|16>>
    <associate|auto-18|<tuple|2.3.4.1|17>>
    <associate|auto-19|<tuple|2.4|17>>
    <associate|auto-2|<tuple|1.1|7>>
    <associate|auto-20|<tuple|2.4.1|18>>
    <associate|auto-21|<tuple|2.4.2|18>>
    <associate|auto-22|<tuple|3|19>>
    <associate|auto-23|<tuple|3.1|19>>
    <associate|auto-24|<tuple|3.1.1|19>>
    <associate|auto-25|<tuple|3.1.2|19>>
    <associate|auto-26|<tuple|3.1.3|19>>
    <associate|auto-27|<tuple|3.2|20>>
    <associate|auto-28|<tuple|3.2.1|20>>
    <associate|auto-29|<tuple|3.2.2|20>>
    <associate|auto-3|<tuple|1.2|8>>
    <associate|auto-30|<tuple|3.2.3|20>>
    <associate|auto-31|<tuple|3.2.4|20>>
    <associate|auto-32|<tuple|3.2.5|21>>
    <associate|auto-33|<tuple|3.2.6|21>>
    <associate|auto-34|<tuple|3.2.7|21>>
    <associate|auto-35|<tuple|3.2.8|21>>
    <associate|auto-36|<tuple|3.2.9|21>>
    <associate|auto-37|<tuple|3.2.10|21>>
    <associate|auto-38|<tuple|3.2.11|22>>
    <associate|auto-39|<tuple|3.3|22>>
    <associate|auto-4|<tuple|1.2.1|8>>
    <associate|auto-40|<tuple|3.3.1|22>>
    <associate|auto-41|<tuple|3.3.2|23>>
    <associate|auto-42|<tuple|3.3.3|23>>
    <associate|auto-43|<tuple|3.3.4|24>>
    <associate|auto-44|<tuple|3.3.5|26>>
    <associate|auto-45|<tuple|3.3.6|26>>
    <associate|auto-46|<tuple|3.3.7|27>>
    <associate|auto-47|<tuple|3.3.7.1|27>>
    <associate|auto-48|<tuple|3.3.7.2|28>>
    <associate|auto-49|<tuple|3.3.7.3|30>>
    <associate|auto-5|<tuple|1.2.2|8>>
    <associate|auto-50|<tuple|3.4|30>>
    <associate|auto-51|<tuple|3.5|31>>
    <associate|auto-52|<tuple|3.5.1|31>>
    <associate|auto-53|<tuple|3.5.2|31>>
    <associate|auto-54|<tuple|3.1|32>>
    <associate|auto-55|<tuple|3.5.2.1|32>>
    <associate|auto-56|<tuple|3.5.2.2|32>>
    <associate|auto-57|<tuple|3.5.2.3|33>>
    <associate|auto-58|<tuple|3.5.2.4|33>>
    <associate|auto-59|<tuple|3.5.2.5|33>>
    <associate|auto-6|<tuple|1.2.3|9>>
    <associate|auto-60|<tuple|3.5.2.6|34>>
    <associate|auto-61|<tuple|3.5.3|34>>
    <associate|auto-62|<tuple|3.5.3.1|35>>
    <associate|auto-63|<tuple|3.6|36>>
    <associate|auto-64|<tuple|3.6.1|36>>
    <associate|auto-65|<tuple|3.6.1.1|36>>
    <associate|auto-66|<tuple|3.6.1.2|39>>
    <associate|auto-67|<tuple|3.6.2|39>>
    <associate|auto-68|<tuple|3.7|39>>
    <associate|auto-69|<tuple|4|41>>
    <associate|auto-7|<tuple|2|11>>
    <associate|auto-70|<tuple|4.1|41>>
    <associate|auto-71|<tuple|4.2|42>>
    <associate|auto-72|<tuple|4.2.1|42>>
    <associate|auto-73|<tuple|4.2.2|42>>
    <associate|auto-74|<tuple|4.2.3|42>>
    <associate|auto-75|<tuple|4.3|42>>
    <associate|auto-76|<tuple|4.3.1|43>>
    <associate|auto-77|<tuple|4.3.2|43>>
    <associate|auto-78|<tuple|4.3.2.1|44>>
    <associate|auto-79|<tuple|4.3.2.2|44>>
    <associate|auto-8|<tuple|2.1|11>>
    <associate|auto-80|<tuple|4.4|45>>
    <associate|auto-81|<tuple|4.4.1|45>>
    <associate|auto-82|<tuple|4.4.1.1|47>>
    <associate|auto-83|<tuple|4.4.1.2|48>>
    <associate|auto-84|<tuple|4.5|48>>
    <associate|auto-85|<tuple|4.5.1|48>>
    <associate|auto-86|<tuple|4.6|49>>
    <associate|auto-87|<tuple|4.7|49>>
    <associate|auto-88|<tuple|4.7.1|49>>
    <associate|auto-89|<tuple|5|51>>
    <associate|auto-9|<tuple|2.1.1|13>>
    <associate|auto-90|<tuple|6|53>>
    <associate|auto-91|<tuple|6.1|54>>
    <associate|auto-92|<tuple|6.1.1|56>>
    <associate|auto-93|<tuple|7|57>>
    <associate|auto-94|<tuple|7.1|57>>
    <associate|auto-95|<tuple|7.1.1|59>>
    <associate|auto-96|<tuple|7.1.2|61>>
    <associate|auto-97|<tuple|7.1.2.1|61>>
    <associate|auto-98|<tuple|7.1.2.2|62>>
    <associate|auto-99|<tuple|7.2|62>>
    <associate|bib-Appel:2015|<tuple|1|97>>
    <associate|bib-Carette:2009|<tuple|3|97>>
    <associate|bib-Coq:manual|<tuple|5|97>>
    <associate|bib-King1993|<tuple|8|97>>
    <associate|bib-Mahboubi:2013|<tuple|9|97>>
    <associate|bib-Mairson:1989|<tuple|10|97>>
    <associate|bib-bip-schnorr|<tuple|17|97>>
    <associate|bib-bitcoin|<tuple|11|97>>
    <associate|bib-f-algebra|<tuple|16|97>>
    <associate|bib-garillot:2009|<tuple|6|97>>
    <associate|bib-gentzen|<tuple|7|97>>
    <associate|bib-libsecp256k1|<tuple|18|97>>
    <associate|bib-oconnor2014|<tuple|14|97>>
    <associate|bib-satoshiScript|<tuple|12|97>>
    <associate|bib-script|<tuple|2|97>>
    <associate|bib-sec2|<tuple|4|97>>
    <associate|bib-sha|<tuple|13|97>>
    <associate|bib-unification|<tuple|15|97>>
    <associate|chapter:preliminaries|<tuple|2|11>>
    <associate|cite_ref-Martelli.Montanari.1976_16-1|<tuple|6.1.1|?>>
    <associate|fig:inheritance|<tuple|8.1|68>>
    <associate|footnote-1|<tuple|1|?>>
    <associate|footnote-2.1|<tuple|2.1|16>>
    <associate|footnote-2.2|<tuple|2.2|23>>
    <associate|footnote-3.1|<tuple|3.1|27>>
    <associate|footnote-3.2|<tuple|3.2|32>>
    <associate|footnr-2.1|<tuple|2.1|16>>
    <associate|footnr-2.2|<tuple|2.2|23>>
    <associate|footnr-3.1|<tuple|3.1|27>>
    <associate|footnr-3.2|<tuple|3.2|32>>
    <associate|full-adder-LHS|<tuple|3.3|26>>
    <associate|full-adder-RHS|<tuple|3.2|25>>
    <associate|full-adder-spec|<tuple|3.1|25>>
    <associate|ss:AssertMerkleRoot|<tuple|4.3.2|43>>
    <associate|ss:BTDenotationalSemantics|<tuple|4.4.1.1|47>>
    <associate|ss:BTMerkleRoots|<tuple|4.4.1.2|48>>
    <associate|ss:BitcoinPrimitives|<tuple|9.3|83>>
    <associate|ss:BitcoinTransactions|<tuple|4.4.1|45>>
    <associate|ss:DAGs|<tuple|7.1|57>>
    <associate|ss:DenotationalSemanticsOfFullSimplicity|<tuple|9.2.3|80>>
    <associate|ss:Deserialization|<tuple|6.2|?>>
    <associate|ss:ELDenotationalSemantics|<tuple|A.1|89>>
    <associate|ss:FreeMonadicDeserialization|<tuple|9.2.6.1|82>>
    <associate|ss:Haskell-DAG|<tuple|9.2.6.2|83>>
    <associate|ss:Haskell-Serialization|<tuple|9.2.6|81>>
    <associate|ss:ListFunctors|<tuple|2.2.2|13>>
    <associate|ss:MonadZero|<tuple|2.3.4|16>>
    <associate|ss:RepresentingValuesAsCellArrays|<tuple|3.5.1|31>>
    <associate|ss:Serialization|<tuple|7.2|62>>
    <associate|ss:bitOps|<tuple|3.3.1|22>>
    <associate|ss:cmr|<tuple|3.7|39>>
    <associate|ss:coqArith|<tuple|8.3.2|67>>
    <associate|ss:coqInitial|<tuple|8.2.1|65>>
    <associate|ss:haskellLoop|<tuple|9.1.5.4|78>>
    <associate|ss:inflate|<tuple|7.1.2.2|62>>
    <associate|ss:monadicSemantics|<tuple|4.1|41>>
    <associate|ss:optionMonad|<tuple|2.3.4.1|17>>
    <associate|ss:pruning|<tuple|4.3.2.1|44>>
    <associate|ss:salted|<tuple|4.3.2.2|44>>
    <associate|ss:typeInference|<tuple|7.1.1|59>>
    <associate|ss:unboundedLoop|<tuple|6.1|54>>
    <associate|thm:CSCT|<tuple|3.3|30>>
    <associate|v:checkSigHashAll|<tuple|8.6.6|?>>
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

      bip-schnorr

      unification

      Mairson:1989

      f-algebra

      Mahboubi:2013

      garillot:2009

      Appel:2015

      Carette:2009

      libsecp256k1

      bip-schnorr

      oconnor2014
    </associate>
    <\associate|figure>
      <tuple|normal|Example state of the Bit Machine.|<pageref|auto-54>>

      <tuple|normal|The inheritance hierarchy of algebras for Simplicity's
      partial extensions in Coq.|<pageref|auto-116>>
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

      <with|par-left|<quote|1tab>|3.3.7<space|2spc>Elliptic Curve Operations
      on secp256k1 <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-46>>

      <with|par-left|<quote|2tab>|3.3.7.1<space|2spc>libsecp256k1
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-47>>

      <with|par-left|<quote|2tab>|3.3.7.2<space|2spc>libsecp256k1 in
      Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-48>>

      <with|par-left|<quote|2tab>|3.3.7.3<space|2spc>Schnorr Signature
      Validation <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-49>>

      3.4<space|2spc>Completeness Theorem
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-50>

      3.5<space|2spc>Operational Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-51>

      <with|par-left|<quote|1tab>|3.5.1<space|2spc>Representing Values as
      Cell Arrays <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-52>>

      <with|par-left|<quote|1tab>|3.5.2<space|2spc>Bit Machine
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-53>>

      <with|par-left|<quote|2tab>|3.5.2.1<space|2spc>Frame Instructions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-55>>

      <with|par-left|<quote|2tab>|3.5.2.2<space|2spc>Active Write Frame
      Instructions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-56>>

      <with|par-left|<quote|2tab>|3.5.2.3<space|2spc>Active Read Frame
      Instructions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-57>>

      <with|par-left|<quote|2tab>|3.5.2.4<space|2spc>Abort Instruction
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-58>>

      <with|par-left|<quote|2tab>|3.5.2.5<space|2spc>Bit Machine Programs
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-59>>

      <with|par-left|<quote|2tab>|3.5.2.6<space|2spc>Crashing the Bit Machine
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-60>>

      <with|par-left|<quote|1tab>|3.5.3<space|2spc>Executing Simplicity
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-61>>

      <with|par-left|<quote|2tab>|3.5.3.1<space|2spc>Tail Composition
      Optimisation (TCO) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-62>>

      3.6<space|2spc>Static Analysis <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-63>

      <with|par-left|<quote|1tab>|3.6.1<space|2spc>Space Resources
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-64>>

      <with|par-left|<quote|2tab>|3.6.1.1<space|2spc>Maximum Cell Count Bound
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-65>>

      <with|par-left|<quote|2tab>|3.6.1.2<space|2spc>Maximum Frame Count
      Bound <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-66>>

      <with|par-left|<quote|1tab>|3.6.2<space|2spc>Time Resources
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-67>>

      3.7<space|2spc>Commitment Merkle Root
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-68>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Simplicity
      Extensions> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-69><vspace|0.5fn>

      4.1<space|2spc>Monadic Semantics <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-70>

      4.2<space|2spc>Witness <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-71>

      <with|par-left|<quote|1tab>|4.2.1<space|2spc>Elided Computation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-72>>

      <with|par-left|<quote|1tab>|4.2.2<space|2spc>Witness Merkle Root
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-73>>

      <with|par-left|<quote|1tab>|4.2.3<space|2spc>Type Inference with
      Witness <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-74>>

      4.3<space|2spc>Assertions and Failure
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-75>

      <with|par-left|<quote|1tab>|4.3.1<space|2spc>Denotational Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-76>>

      <with|par-left|<quote|1tab>|4.3.2<space|2spc>Merkle Roots
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-77>>

      <with|par-left|<quote|2tab>|4.3.2.1<space|2spc>Pruning Unused
      <with|font-family|<quote|ss>|case> Branches
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-78>>

      <with|par-left|<quote|2tab>|4.3.2.2<space|2spc>Salted Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-79>>

      4.4<space|2spc>Blockchain Primitives
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-80>

      <with|par-left|<quote|1tab>|4.4.1<space|2spc>Bitcoin Transactions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-81>>

      <with|par-left|<quote|2tab>|4.4.1.1<space|2spc>Denotational Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-82>>

      <with|par-left|<quote|2tab>|4.4.1.2<space|2spc>Merkle Roots
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-83>>

      4.5<space|2spc>Simplicity Programs <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-84>

      <with|par-left|<quote|1tab>|4.5.1<space|2spc>Example:
      <rigid|<with|mode|<quote|text>|<with|font-family|<quote|ss>|font-shape|<quote|right>|checkSigHashAll>>>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-85>>

      4.6<space|2spc>Schnorr Signature Aggregation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-86>

      4.7<space|2spc>Malleability <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-87>

      <with|par-left|<quote|1tab>|4.7.1<space|2spc>Transaction Weight
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-88>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Jets>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-89><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Delegation>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-90><vspace|0.5fn>

      6.1<space|2spc>Unbounded Loops <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-91>

      <with|par-left|<quote|1tab>|6.1.1<space|2spc>Adding a
      <with|font-family|<quote|ss>|loop> primitive to Simplicity?
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-92>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|7<space|2spc>Type
      Inference and Serialization> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-93><vspace|0.5fn>

      7.1<space|2spc>Explicit Simplicity DAGs
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-94>

      <with|par-left|<quote|1tab>|7.1.1<space|2spc>Type Inference
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-95>>

      <with|par-left|<quote|1tab>|7.1.2<space|2spc>Reconstructing Simplicity
      Expressions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-96>>

      <with|par-left|<quote|2tab>|7.1.2.1<space|2spc>syncase
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-97>>

      <with|par-left|<quote|2tab>|7.1.2.2<space|2spc>inflate
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-98>>

      7.2<space|2spc>Serialization <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-99>

      <with|par-left|<quote|1tab>|7.2.1<space|2spc>Serialization of Bit
      Strings and Positive Numbers <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-100>>

      <with|par-left|<quote|1tab>|7.2.2<space|2spc>Serialization of
      Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-101>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|8<space|2spc>Coq
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-102><vspace|0.5fn>

      8.1<space|2spc>Simplicity Types <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-103>

      8.2<space|2spc>Simplicity Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-104>

      <with|par-left|<quote|1tab>|8.2.1<space|2spc>The ``Initial''
      Representation of Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-105>>

      <with|par-left|<quote|1tab>|8.2.2<space|2spc>The ``Final''
      Representation of Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-106>>

      <with|par-left|<quote|2tab>|8.2.2.1<space|2spc>Simplicity Algebras
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-107>>

      <with|par-left|<quote|2tab>|8.2.2.2<space|2spc>The ``Final''
      Representation <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-108>>

      <with|par-left|<quote|2tab>|8.2.2.3<space|2spc>Constructing ``Final''
      Terms <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-109>>

      <with|par-left|<quote|1tab>|8.2.3<space|2spc>Why two representations of
      Terms? <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-110>>

      8.3<space|2spc>Example Simplicity Expressions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-111>

      <with|par-left|<quote|1tab>|8.3.1<space|2spc>Bits
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-112>>

      <with|par-left|<quote|1tab>|8.3.2<space|2spc>Arithmetic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-113>>

      <with|par-left|<quote|1tab>|8.3.3<space|2spc>SHA256
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-114>>

      8.4<space|2spc>The Hierarchy of Simplicity Language Extensions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-115>

      <with|par-left|<quote|1tab>|8.4.1<space|2spc>Witness
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-117>>

      <with|par-left|<quote|1tab>|8.4.2<space|2spc>Assertion
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-118>>

      <with|par-left|<quote|1tab>|8.4.3<space|2spc>Delegation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-119>>

      <with|par-left|<quote|1tab>|8.4.4<space|2spc>Primitives
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-120>>

      <with|par-left|<quote|2tab>|8.4.4.1<space|2spc>Bitcoin
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-121>>

      <with|par-left|<quote|1tab>|8.4.5<space|2spc>Jets
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-122>>

      <with|par-left|<quote|1tab>|8.4.6<space|2spc>Full Simplicity
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-123>>

      8.5<space|2spc>Merkle Roots <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-124>

      8.6<space|2spc>The Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-125>

      <with|par-left|<quote|1tab>|8.6.1<space|2spc>Bit Machine Code
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-126>>

      <with|par-left|<quote|2tab>|8.6.1.1<space|2spc>Bit Machine Programs
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-127>>

      <with|par-left|<quote|1tab>|8.6.2<space|2spc>Translating Simplicity to
      the Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-128>>

      <with|par-left|<quote|1tab>|8.6.3<space|2spc>Static Analysis
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-129>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|9<space|2spc>Haskell
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-130><vspace|0.5fn>

      9.1<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|Simplicity-Core>
      library <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-131>

      <with|par-left|<quote|1tab>|9.1.1<space|2spc>Simplicity Types
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-132>>

      <with|par-left|<quote|1tab>|9.1.2<space|2spc>Simplicity Terms
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-133>>

      <with|par-left|<quote|1tab>|9.1.3<space|2spc>Merkle Roots
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-134>>

      <with|par-left|<quote|1tab>|9.1.4<space|2spc>Tensors
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-135>>

      <with|par-left|<quote|1tab>|9.1.5<space|2spc>Example Simplicity
      Expressions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-136>>

      <with|par-left|<quote|2tab>|9.1.5.1<space|2spc>Bits
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-137>>

      <with|par-left|<quote|2tab>|9.1.5.2<space|2spc>Multi-bit Words
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-138>>

      <with|par-left|<quote|2tab>|9.1.5.3<space|2spc>Generic
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-139>>

      <with|par-left|<quote|2tab>|9.1.5.4<space|2spc>Loop
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-140>>

      <with|par-left|<quote|1tab>|9.1.6<space|2spc>Libraries of Simplicity
      Expressions <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-141>>

      <with|par-left|<quote|2tab>|9.1.6.1<space|2spc>SHA-256
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-142>>

      <with|par-left|<quote|2tab>|9.1.6.2<space|2spc>LibSecp256k1
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-143>>

      <with|par-left|<quote|1tab>|9.1.7<space|2spc>The Bit Machine
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-144>>

      <with|par-left|<quote|2tab>|9.1.7.1<space|2spc>Translating Simplicity
      to the Bit Machine <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-145>>

      <with|par-left|<quote|2tab>|9.1.7.2<space|2spc>Static Analysis
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-146>>

      9.2<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|Simplicity-Indef>
      library <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-147>

      <with|par-left|<quote|1tab>|9.2.1<space|2spc>Primitive Signature
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-148>>

      <with|par-left|<quote|1tab>|9.2.2<space|2spc>Primitive Terms
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-149>>

      <with|par-left|<quote|1tab>|9.2.3<space|2spc>Denotational Semantics of
      Full Simplicity <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-150>>

      <with|par-left|<quote|1tab>|9.2.4<space|2spc>Known Discounted Jets
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-151>>

      <with|par-left|<quote|1tab>|9.2.5<space|2spc>Type Inference
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-152>>

      <with|par-left|<quote|1tab>|9.2.6<space|2spc>Serialization
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-153>>

      <with|par-left|<quote|2tab>|9.2.6.1<space|2spc>Free Monadic
      Deserializaiton <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-154>>

      <with|par-left|<quote|2tab>|9.2.6.2<space|2spc>Serialization of
      Simplicity DAGs <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-155>>

      9.3<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|Simplicity-Bitcoin>
      Libary <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-156>

      9.4<space|2spc><with|font-family|<quote|tt>|language|<quote|verbatim>|Simplicity>
      Library <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-157>

      <with|par-left|<quote|1tab>|9.4.1<space|2spc>CheckSigHashAll
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-158>>

      9.5<space|2spc>Simplicity <with|font-family|<quote|tt>|language|<quote|verbatim>|testsuite>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-159>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|10<space|2spc>C
      Library Guide> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-160><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Appendix
      A<space|2spc>Elements Application> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-161><vspace|0.5fn>

      A.1<space|2spc>Denotational Semantics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-162>

      <with|par-left|<quote|1tab>|A.1.1<space|2spc>Null Data
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-163>>

      <with|par-left|<quote|1tab>|A.1.2<space|2spc>Merkle Roots
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-164>>

      <with|par-left|<quote|1tab>|A.1.3<space|2spc>Serialization
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-165>>

      A.2<space|2spc>Jets <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-166>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Appendix
      B<space|2spc>Alternative Serialization of Simplicity DAGs>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-167><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-168><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>