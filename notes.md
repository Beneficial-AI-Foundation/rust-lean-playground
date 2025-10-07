# Notes

This file contains notes concerning the experiment of verifying Rust code with Lean.

- In many cases there were multiple versions of spec theorems that were useful for different purposes. In paticular often a bit vector spec and a natural number spec were convenient for different uses. 
- In many cases the Lean API was lacking in required places and theorems needed to be added.
- Writing proofs was very quick when the API was properly setup.
- Claude code was very good at writing the spec theorems on many occasions.
- Both Aeneas and Hax have advantages and problems when translating to Lean.

## Suggestions for the next step

- Choose a substatial project to work with, the toolchain is ready for this althought there will be many small difficulties along the way.
- Consistently improve the Lean API of each relevant topic.
- Attempt to deploy LLMs at scale to both write specs and proofs.

