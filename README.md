# LeanMachineLearning catalogue

Evidence about [LeanMachineLearning](https://github.com/LeanMachineLearning/LML)'s definitions,
declared from outside the library with [TrustAnnotations](https://github.com/LeanTrustBuilders/annotations):
where each definition is meant to apply (`@[domain]`), what it is determined up to (`@[up_to]`),
characterizations stated by one theorem, specifications and examples. Part of the
[LeanTrustBuilders](https://github.com/LeanTrustBuilders) suite; see `well-definedness.md` in the
design notes.

| module | about |
|---|---|
| `LMLCatalogue.Bandits` | what the regret bound of UCB rests on: the domains of `empMean'` and `ucbWidth'` (an arm pulled at least once) and of `regret` and `gap` (integrable means); `argmax` determined up to ties; characterizations of `Function.max`, of Round-Robin's arm and of the regret as a sum of gaps; specifications of `argmax`, UCB's arm, `gap` and `regret`; an example of an algorithm-environment sequence |
| `LMLCatalogue.Discharger` | `lml_catalogue_discharger`: the facts that show the domains in LeanMachineLearning's bandit statements (subgaussian rewards have integrable means, the regret of an algorithm-environment sequence is integrable), a `solve_by_elim` the well-definedness analyzer tries after its default dischargers |

The catalogue imports the [Mathlib catalogue](https://github.com/LeanTrustBuilders/mathlib-catalogue),
built against LeanMachineLearning's Mathlib, so that the analysis also uses its domains of Mathlib's
definitions (the Bochner integral, the logarithm).

LeanMachineLearning's theorems cannot carry an annotation written outside it, so specifications and
characterizations are restated here, each proved by the lemma it restates, or directly where the
library has none. Domains and relations need no restatement: `attribute [domain …] d` works on a
definition of another library.

## How it reaches a site

CI builds the catalogue against LeanMachineLearning at the commit in `lakefile.toml`, extracts its
dataset with the [extractor](https://github.com/LeanTrustBuilders/extractor), runs the
well-definedness analysis of every theorem of `LeanMachineLearning.Online.Bandit`, and publishes the
dataset as the release `dataset-<commit12>`. [site-pilot](https://github.com/LeanTrustBuilders/site-pilot)
merges it into LeanMachineLearning's dataset of the same commit (`evidence-core merge`), which checks
that the two agree on every declaration they share, and builds the site and the claim pages from the
result.

## Adding to it

A new module under `LMLCatalogue/`, imported by `LMLCatalogue.lean`. Keep LeanMachineLearning at the
commit site-pilot extracts (its `main`), and the manifest's other packages at the revisions
LeanMachineLearning's own manifest pins.
