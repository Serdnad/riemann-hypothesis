module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle344
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle346
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle345
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameOff ((A0 J).pl v).1 (J.pt std j hj La).1 (J.pt std j hj Lb).1 ∧ ∀ v', v' ≠ v → len (sysS H X std) v' j La.2 = len (sysS H X std) v' j Lb.2) := by
  first | exact @GlobalTheory.TwV.Xc.sameOff_len_of_sameAway | exact GlobalTheory.TwV.Xc.sameOff_len_of_sameAway | (intros; apply GlobalTheory.TwV.Xc.sameOff_len_of_sameAway <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eigenvalue_arithmeticElement_at_site : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → FillAt (hT := hT) (H := H) (X := X) std j hj → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) ∈ TaylorLogMetric.Qbar ∧ kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ = TaylorLogMetric.lamC S.lam (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) * ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La))) := by
  first | exact @GlobalTheory.TwV.Xc.kapG_at_site | exact GlobalTheory.TwV.Xc.kapG_at_site | (intros; apply GlobalTheory.TwV.Xc.kapG_at_site <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.level_badPrimes_coprime_residueChar : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => Nat.Coprime (t.rd u μ).lev (D.what₂.places.resChar w) ∧ (∀ Q ∈ GlobalTheory.TwU.ssRec t u μ, (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ (∀ v ∈ Formalism.L2.Col.plUnder D.host.F (GlobalTheory.TwU.ssRec t u μ), (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, GlobalTheory.TwU.UnderSB t μ v → (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) := by
  first | exact @GlobalTheory.TwV.Xc.SBad.bad_prime_to_p | exact GlobalTheory.TwV.Xc.SBad.bad_prime_to_p | (intros; apply GlobalTheory.TwV.Xc.SBad.bad_prime_to_p <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepCharts_places_firstFactor_eq_stepZero : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) v, ((I.at' j hj).st.loc β).pl v = (A0 J).pl v ∧ ∀ x, phiA ((I.at' j hj).st.loc β) v x = phiA (A0 J) v x) := by
  first | exact @GlobalTheory.TwV.Xc.chart_places_firstFactor_eq_zero | exact GlobalTheory.TwV.Xc.chart_places_firstFactor_eq_zero | (intros; apply GlobalTheory.TwV.Xc.chart_places_firstFactor_eq_zero <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZero_latticeTuple_move_by_rational_isometry : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (c : (sysS H X std).Lv.comp 0) (La : ((sysS H X std).Pj 0).Tup) (γ : ((sysS H X std).Lv.lev 0 c).Γ), ((sysS H X std).Pj 0).IsLatTup La → ∃ g κ, MoveBy std J 0 (Nat.zero_le _) c La γ g κ) := by
  first | exact @GlobalTheory.TwV.Xc.moveBy_zero | exact GlobalTheory.TwV.Xc.moveBy_zero | (intros; apply GlobalTheory.TwV.Xc.moveBy_zero <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepCharacter_uniformizingIdele_mem_coeffField : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => KIn t → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, ∃ r : D.what₂.LL, D.what₂.embLL r = S.muT (j + 1) π) := by
  first | exact @GlobalTheory.TwV.Xc.MuLL.mu_mem_LL | exact GlobalTheory.TwV.Xc.MuLL.mu_mem_LL | (intros; apply GlobalTheory.TwV.Xc.MuLL.mu_mem_LL <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.character_detIdeal_kernelLattice_latticeTuple : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j La)) = (∏ τ, TaylorLogMetric.embT D τ (gMat J j hj (d.gam j hj La)).det)⁻¹ * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ∧ (∏ τ, TaylorLogMetric.embT D τ (gMat J j hj (d.gam j hj La)).det) ≠ 0) := by
  first | exact @GlobalTheory.TwV.DelB.chi_detId_kerN | exact GlobalTheory.TwV.DelB.chi_detId_kerN | (intros; apply GlobalTheory.TwV.DelB.chi_detId_kerN <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.decomposition_unitary_mul_star_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j La, d.eM j La * star (d.eM j La) = 1) := by
  first | exact @GlobalTheory.TwV.DelB.Dec.eM_mul_star | exact GlobalTheory.TwV.DelB.Dec.eM_mul_star | (intros; apply GlobalTheory.TwV.DelB.Dec.eM_mul_star <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ k (hk : k ≤ D.R.m), (gMat J k hk 1).det * D.host.conj (gMat J k hk 1).det = 1 ∧ ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk), (gMat J k hk γ).det = γ.1.det * (gMat J k hk 1).det ∧ γ.1.det * D.host.conj γ.1.det = 1) := by
  first | exact @GlobalTheory.TwV.DelB.gMat_det | exact GlobalTheory.TwV.DelB.gMat_det | (intros; apply GlobalTheory.TwV.DelB.gMat_det <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.pullback_scalar_ne_zero_latticeTuple_pair : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std), ∀ j < D.R.m, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → d.sP S j La La' ≠ 0) := by
  first | exact @GlobalTheory.TwV.DelB.pullbackScalar_ne_zero | exact GlobalTheory.TwV.DelB.pullbackScalar_ne_zero | (intros; apply GlobalTheory.TwV.DelB.pullbackScalar_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.systemWeights_eq_shifted_character_exponents : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m), (sysS H X std).Lv.comp (j + 1) → FillAt (hT := hT) (H := H) (X := X) std j hj) := by
  first | exact @GlobalTheory.TwV.Xc.fillAt_of_comp | exact GlobalTheory.TwV.Xc.fillAt_of_comp | (intros; apply GlobalTheory.TwV.Xc.fillAt_of_comp <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.site_localIdentifications_eq_stepZero : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).iw v = (lev0At g u w hg).A.iw v) ∧ (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).pl v = (lev0At g u w hg).A.pl v) ∧ (∀ j hj β β', (((Z.inTw Fl ht Gt).at' j hj).st.loc β).B = (((Z.inTw Fl ht Gt).at' j hj).st.loc β').B) ∧ (∀ j hj, ((Z.inTw Fl ht Gt).at' j hj).st.pos = Gt.gat_pos u w hg) ∧ (∀ j hj β, GlobalTheory.TwV.SplAlg (((Z.inTw Fl ht Gt).at' j hj).st.loc β)) ∧ GlobalTheory.TwV.SplAlg (lev0At g u w hg).A := by
  exact @GlobalTheory.Proof.LocOfSite.loc_eq_step0
end
