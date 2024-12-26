# CS 6120 — Advanced Compilers Project

This repository contains my personal projects and experiments while taking [**CS 6120 (Advanced Compilers)**](https://www.cs.cornell.edu/courses/cs6120/2023fa/self-guided/). The goal is to deepen my understanding of compiler construction, optimizations, and advanced language processing techniques by implementing various components of a compiler toolchain.
```
.
├── bril                                          // Submodule to a forked version of https://github.com/sampsyo/bril
├── Cargo.lock
├── Cargo.toml
├── common                                        // Some common utilites
│   ├── Cargo.toml
│   └── src
│       ├── cfg
│       ├── cfg.rs
│       └── lib.rs
├── dataflow_analysis                             // Data flow dataflow analysis
│   ├── Cargo.toml
│   └── src
│       └── lib.rs
├── driver                                        // Helper application to consume and transform bril programs
│   ├── Cargo.toml
│   └── src
│       └── main.rs
└── optimizations                                 // Some optimization example passes
   ├── Cargo.toml
   └── src
       ├── lib.rs
       ├── local_dead_code_elimination.rs
       └── local_value_numbering.rs
```
## License
The MIT License

Copyright 2024 Kevin Joseph

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
