## What is JabberHive?
JabberHive is a modular Reply Bot system. All "modules" are in fact separate
programs linked together using the JabberHive Protocol. Please refer to the
protocol for more information.

## Component Description
* Server for a JabberHive network.
* Handles learning & replying using K-order Markov Chains, with k >= 2.
* Knowledge is kept in RAM.

## JabberHive Protocol Compatibility
* **Protocol Version(s):** 1 (Targeted).
* **Inbound Connections:** Multiple.
* **Outbound Connections:** None.
* **Pipelining:** No.
* **Behavior:** Server.

## Dependencies
- POSIX compliant OS.
- C compiler (with C99 support).
- (GNU) make.
