/-
# Tex2lean

Root module. Importing `Tex2lean` must pull in the headline theorem, so that
`import Tex2lean` and a bare `lake build` both compile *and expose* the result.

Keep this file a pure aggregation of area roots — put content in the modules.
-/

import Tex2lean.Model.Theorem
