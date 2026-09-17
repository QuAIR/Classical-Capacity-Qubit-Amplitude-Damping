import AmplitudeDamping.Definitions
import AmplitudeDamping.ConvexRoof
import AmplitudeDamping.Channel
import AmplitudeDamping.QubitState
import AmplitudeDamping.QubitEntropy
import AmplitudeDamping.FixedExcitation
import AmplitudeDamping.ScalarCurve
import AmplitudeDamping.EqualExcitation
import AmplitudeDamping.HolevoReduction
import AmplitudeDamping.Triangular.Statement
import AmplitudeDamping.Triangular.LogDet
import AmplitudeDamping.Triangular.LogDetCalculus
import AmplitudeDamping.Triangular.EntropyReduction
import AmplitudeDamping.Triangular.EntropyIntegral
import AmplitudeDamping.Triangular.Dephasing
import AmplitudeDamping.Triangular.ScalarCompression
import AmplitudeDamping.Triangular.ScalarBoundary
import AmplitudeDamping.Triangular.TraceCompression
import AmplitudeDamping.Triangular.ScalarNormalization
import AmplitudeDamping.Triangular.GramEntropy

/-!
# Formalization of strong additivity for amplitude damping

This is the root import for the project.  The modules deliberately separate
the analytic triangular-block inequality from its information-theoretic
consequences.
-/
