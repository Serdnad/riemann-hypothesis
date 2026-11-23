module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefIntegralEq
public import Mathlib.LinearAlgebra.Matrix.Rank
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle360
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle462
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdelicUnitaryProdLocalPointsMulLatticeStab
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle400
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle372
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle017
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle466
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle405
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle441
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle402
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle467
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle469
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Move

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem integral_ker_move (W : G.Weil) (M : Vol G) (p : Pair T) (hp : p.InRange D.R.m)
    {K : Subgroup (GL (Fin (G.V p.small).rank) (Lev.EAf D))} (hM : M.IsAt p.small K)
    (k : GA D (G.V p.small)) (k' : GA D (G.V p.big))
    (hk : MeasurePreserving (fun g : GA D (G.V p.small) => g * k) (M.ν p.small) (M.ν p.small))
    (hk' : Measurable fun g : GA D (G.V p.small) => g * k⁻¹)
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (F : GA D (G.V p.small) → ℂ) (hF : ∀ γ ∈ GQ (G.V p.small), ∀ g, F (γ * g) = F g) (h : GA D (G.V p.big)) :
    ∫ g in M.fd p.small, W.ker p f g (h * k') * F g ∂M.ν p.small =
      ∫ g in M.fd p.small, W.ker p (W.om p (G.toPair p k k') f) g h * F (g * k) ∂M.ν p.small := by
  rw [← setIntegral_fd_mul_right M hM k hk hk' (fun g => W.ker p f g (h * k') * F g) ?_]
  · congr 1
    funext g
    rw [ker_mul]
  · intro γ hγ g
    have e := ker_rat_left W p hp f hf γ hγ 1 (one_mem _) g (h * k')
    rw [one_mul] at e
    simp only [e, hF γ hγ g]

theorem integral_ker_left (W : G.Weil) (M : Vol G) (p : Pair T) (hp : p.InRange D.R.m)
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (F : GA D (G.V p.small) → ℂ) (γ : GA D (G.V p.big)) (hγ : γ ∈ GQ (G.V p.big)) (h : GA D (G.V p.big)) :
    ∫ g in M.fd p.small, W.ker p f g (γ * h) * F g ∂M.ν p.small =
      ∫ g in M.fd p.small, W.ker p f g h * F g ∂M.ν p.small := by
  congr 1
  funext g
  have e := ker_rat_left W p hp f hf 1 (one_mem _) γ hγ g h
  rw [one_mul] at e
  rw [e]

end Move

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Paths

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem pathLift_column_leftInvariant (W : G.Weil) (M : Vol G) (t : T) : ∀ (n : ℕ), n ≤ D.R.m →
    ∀ (f : ∀ j : Fin n, Sch G (.col t j)), (∀ j : Fin n, IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (f j)) →
    ∀ (φ : Fn G (.top 0)), (∀ γ ∈ GQ (G.V (.top 0)), ∀ g, φ (γ * g) = φ g) →
    ∀ γ ∈ GQ (G.V (.top n)), ∀ h,
      liftP W M (colPath t n) (colFam t n f) φ (γ * h) = liftP W M (colPath t n) (colFam t n f) φ h
  | 0, _, _, _, _, hφ, γ, hγ, h => hφ γ hγ h
  | n + 1, hn, f, hf, φ, _, γ, hγ, h => by
    show liftA W M (.col t n) (f (Fin.last n)) _ (γ * h) = liftA W M (.col t n) (f (Fin.last n)) _ h
    simp only [liftA_apply]
    exact integral_ker_left W M (.top t n) hn _ (hf (Fin.last n)) _ γ hγ h

theorem pathLift_row_leftInvariant (W : G.Weil) (M : Vol G) : ∀ (n : ℕ), n ≤ D.R.m →
    ∀ (f : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (f i)) →
    ∀ (F : Fn G (.grid 0 D.R.m)), (∀ γ ∈ GQ (G.V (.grid 0 D.R.m)), ∀ g, F (γ * g) = F g) →
    ∀ γ ∈ GQ (G.V (.grid n D.R.m)), ∀ h,
      liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F (γ * h) = liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F h
  | 0, _, _, _, _, hF, γ, hγ, h => hF γ hγ h
  | n + 1, hn, f, hf, F, _, γ, hγ, h => by
    show liftA W M (.right n D.R.m) (f (Fin.last n)) _ (γ * h) = liftA W M (.right n D.R.m) (f (Fin.last n)) _ h
    simp only [liftA_apply]
    exact integral_ker_left W M (.chi n D.R.m) ⟨hn, le_rfl⟩ _ (hf (Fin.last n)) _ γ hγ h

theorem pathLift_column_translate (W : G.Weil) (M : Vol G) (t : T) (κ : ∀ n : ℕ, GA D (G.V (.top n))) : ∀ (n : ℕ), n ≤ D.R.m →
    (∀ j, j < n → (∃ K, M.IsAt (.top j) K) ∧
      MeasurePreserving (fun g : GA D (G.V (.top j)) => g * κ j) (M.ν (.top j)) (M.ν (.top j)) ∧
      Measurable (fun g : GA D (G.V (.top j)) => g * (κ j)⁻¹)) →
    ∀ (f f' : ∀ j : Fin n, Sch G (.col t j)), (∀ j : Fin n, IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (f j)) →
    (∀ j : Fin n, W.om (.top t j) (G.toPair (.top t j) (κ j) (κ (j + 1))) (f j) = f' j) →
    ∀ (φ : Fn G (.top 0)), (∀ γ ∈ GQ (G.V (.top 0)), ∀ g, φ (γ * g) = φ g) →
    ∀ h, liftP W M (colPath t n) (colFam t n f) φ (h * κ n) =
      liftP W M (colPath t n) (colFam t n f') (fun x => φ (x * κ 0)) h := by
  intro n
  induction n with
  | zero =>
    intros
    rfl
  | succ n ih =>
    intro hn hκ f f' hf hff φ hφ h
    obtain ⟨⟨K, hK⟩, hm, hm'⟩ := hκ n (Nat.lt_succ_self n)
    show liftA W M (.col t n) (f (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => f j.castSucc) φ) (h * κ (n + 1)) =
      liftA W M (.col t n) (f' (Fin.last n))
        (liftP W M (colPath t n) (colFam t n fun j => f' j.castSucc) (fun x => φ (x * κ 0))) h
    simp only [liftA_apply]
    have e := integral_ker_move W M (.top t n) hn hK (κ n) (κ (n + 1)) hm hm' (f (Fin.last n)) (hf (Fin.last n)) _
      (pathLift_column_leftInvariant W M t n (by omega) _ (fun j => hf j.castSucc) φ hφ) h
    refine e.trans ?_
    rw [← hff (Fin.last n)]
    congr 1
    funext g
    rw [ih (by omega) (fun j hj => hκ j (by omega)) _ _ (fun j => hf j.castSucc)
      (fun j => hff j.castSucc) φ hφ g]
    rfl

theorem pathLift_row_translate (W : G.Weil) (M : Vol G) (κ : ∀ n : ℕ, GA D (G.V (.grid n D.R.m))) : ∀ (n : ℕ), n ≤ D.R.m →
    (∀ i, i < n → (∃ K, M.IsAt (.grid i D.R.m) K) ∧
      MeasurePreserving (fun g : GA D (G.V (.grid i D.R.m)) => g * κ i) (M.ν (.grid i D.R.m)) (M.ν (.grid i D.R.m)) ∧
      Measurable (fun g : GA D (G.V (.grid i D.R.m)) => g * (κ i)⁻¹)) →
    ∀ (f f' : ∀ i : Fin n, Sch G (.right i D.R.m)),
      (∀ i : Fin n, IsThetaFunO W.ψ (G.pS (.chi i D.R.m)) (G.pT (.chi i D.R.m)) (f i)) →
    (∀ i : Fin n, W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (κ i) (κ (i + 1))) (f i) = f' i) →
    ∀ (F : Fn G (.grid 0 D.R.m)), (∀ γ ∈ GQ (G.V (.grid 0 D.R.m)), ∀ g, F (γ * g) = F g) →
    ∀ h, liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f) F (h * κ n) =
      liftP W M (rowPath T D.R.m n) (rowFam D.R.m n f') (fun x => F (x * κ 0)) h := by
  intro n
  induction n with
  | zero =>
    intros
    rfl
  | succ n ih =>
    intro hn hκ f f' hf hff F hF h
    obtain ⟨⟨K, hK⟩, hm, hm'⟩ := hκ n (Nat.lt_succ_self n)
    show liftA W M (.right n D.R.m) (f (Fin.last n)) (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f i.castSucc) F)
        (h * κ (n + 1)) =
      liftA W M (.right n D.R.m) (f' (Fin.last n))
        (liftP W M (rowPath T D.R.m n) (rowFam D.R.m n fun i => f' i.castSucc) (fun x => F (x * κ 0))) h
    simp only [liftA_apply]
    have e := integral_ker_move W M (.chi n D.R.m) ⟨hn, le_rfl⟩ hK (κ n) (κ (n + 1)) hm hm' (f (Fin.last n)) (hf (Fin.last n)) _
      (pathLift_row_leftInvariant W M n (by omega) _ (fun i => hf i.castSucc) F hF) h
    refine e.trans ?_
    rw [← hff (Fin.last n)]
    congr 1
    funext g
    rw [ih (by omega) (fun i hi => hκ i (by omega)) _ _ (fun i => hf i.castSucc)
      (fun i => hff i.castSucc) F hF g]
    rfl

end Paths

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Coef

variable {D : D7}

theorem pairVec_mul_real {V : HSp D} (c : CoefA V) (ξ : Module.Dual ℂ c.W) (Ψ : Bridge.Gf V → c.W) {k : GA D V}
    (hk : k ∈ GinfC V) (x : GA D V) :
    pairVec c (ξ ∘ₗ c.ρ k⁻¹) Ψ x = pairVec c ξ Ψ (x * k) := by
  have e : (finHom V).rangeRestrict (x * k) = (finHom V).rangeRestrict x := by
    have hk1 : (finHom V).rangeRestrict k = 1 := Subtype.ext (by simpa using MonoidHom.mem_ker.1 hk)
    rw [map_mul, hk1, mul_one]
  have h3 : c.ρ (x * k)⁻¹ = c.ρ k⁻¹ * c.ρ x⁻¹ := (congrArg c.ρ (mul_inv_rev x k)).trans (c.ρ.map_mul _ _)
  show ξ (c.ρ k⁻¹ (c.ρ x⁻¹ (Ψ ((finHom V).rangeRestrict x)))) =
    ξ (c.ρ (x * k)⁻¹ (Ψ ((finHom V).rangeRestrict (x * k))))
  exact (congrArg (fun A : Module.End ℂ c.W => ξ (A (Ψ ((finHom V).rangeRestrict x)))) h3.symm).trans
    (congrArg (fun z => ξ (c.ρ (x * k)⁻¹ (Ψ z))) e.symm)

theorem ext_cast_mul_real {X Y : LSp D} (e : X = Y) (c : CoefA Y.sp) (v : Bridge.Gf Y.sp → c.W) (η : Module.Dual ℂ c.W)
    {k : GA D X.sp} (hk : k ∈ GinfC X.sp) (g : GA D X.sp) :
    (η ∘ₗ c.ρ (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) k)⁻¹) (c.ext v (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) g)) =
      η (c.ext v (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) (g * k))) := by
  subst e
  exact pairVec_mul_real c η v hk g

end Coef

section Gen

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem formGen_mul_real (t : T) (y : (R.HX t).H) (η : Module.Dual ℂ R.cX.W) {k : GA D (ch.G.V (.grid 0 D.R.m))}
    (hk : k ∈ GinfC (ch.G.V (.grid 0 D.R.m))) (g : GA D (ch.G.V (.grid 0 D.R.m))) :
    formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) k)⁻¹) g =
      formGen ch t y η (g * k) :=
  ext_cast_mul_real (colY_m R.toLevCh) R.cX _ η hk g

end Gen

end GlobalTheory.RowReal
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

theorem meanX_prod_zero_eq : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b)).range μ 𝓨 → ∀ F₁ F₁' F₂ F₂' : WO V W → ℂ, IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₁' → IsThetaFunO ψ V W F₂ → IsThetaFunO ψ V W F₂' → (∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ w : WO V W, (∀ y : Mx D a b, symplO V W w (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₁ u * star (F₁' u) ∂ν) ∂μ = ∫ y, (∫ u in 𝓕, heisO ψ V W (w + GlobalTheory.IsoMean.emb V W P Q y) F₂ u * star (F₂' u) ∂ν) ∂μ) → GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₁' 0) = GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂ 0 * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 F₂' 0) := by
  intro D V W a b P Q hP hQ hiso ψ hψ μ 𝓨 hμ F₁ F₁' F₂ F₂' h₁ h₁' h₂ h₂' H
  obtain ⟨k, B, horth, hdec, huniq, hrat, hsep⟩ := GlobalTheory.T.exists_rational_complement_isotropic_sandwich D V W a b P Q hP hQ hiso ψ hψ
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D 1 k
  haveI : BorelSpace (Mx D 1 k) := ⟨rfl⟩
  obtain ⟨η, 𝓩, hη⟩ := GlobalTheory.MixModel.exists_isCovolOne D 1 k
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank V.rank
  have hμ' : IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 := hμ
  have hν2 : IsAddFundamentalDomain (ratL W V) 𝓕 ν := hν.2.1
  obtain ⟨κ, hκ, hU⟩ := GlobalTheory.T.integral_matrixCoeff_isotropic_eq_mul_mean D V W a b P Q hP hQ hiso k B horth hdec huniq hrat ψ hψ μ 𝓨 hμ' η 𝓩 hη.1 hη.2.1 ν 𝓕
    hν.1 hν2 (GlobalTheory.T.integrable_thetaMatrixCoeff_isotropic_rational D V W a b P Q hP hQ hiso ψ hψ μ hμ.1 ν 𝓕 hν.1 hν2)
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e
  set ι := GlobalTheory.IsoMean.cplx V W B with hι
  have hιrat : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ι c ∈ ratL W V := by
    rintro _ ⟨c, rfl⟩
    exact ⟨_, (GlobalTheory.IsoMean.cplx_rat V W B c).symm⟩
  have hT := @GlobalTheory.ThetaClosed.isThetaFunO_heisO_all D ψ hψ V W

  have hcomp : ∀ (w ξ : WO V W), symplOH V W ξ w = 0 → ∀ G : WO V W → ℂ,
      heisO ψ V W (w + ξ) G = heisO ψ V W ξ (heisO ψ V W w G) := by
    intro w ξ h G
    funext u
    simp only [heisO]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, l2, l1, h, add_zero, add_comm (symplOH V W u w),
      show u + ξ + w = u + (w + ξ) by abel]

  have hcoef : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      ∫ y, (∫ u in 𝓕, heisO ψ V W (ι c + GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) ∂μ =
        κ * ∫ z in 𝓩, ψ (symplO V W (ι z) (ι c)) *
          (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G (ι z) * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G' (ι z))) ∂η := by
    intro c hc G G' hG hG'
    have e1 : ∀ y, heisO ψ V W (ι c + GlobalTheory.IsoMean.emb V W P Q y) G =
        heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) (heisO ψ V W (ι c) G) := fun y =>
      hcomp _ _ (by rw [skew, hH0 _ _ (horth c y), neg_zero]) G
    simp only [e1]
    rw [hU _ G' (hT hG (ι c)) hG']
    congr 1
    congr 1
    funext z
    rw [GlobalTheory.IsoMean.meanX_heisO_rat V W P Q μ 𝓨 ψ G hG (ι c) (hιrat c hc) (horth c) (ι z) (horth z)]
    ring
  set g : (WO V W → ℂ) → (WO V W → ℂ) → Mx D 1 k → ℂ := fun G G' z =>
    GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G (ι z) * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G' (ι z)) with hg
  have hιc : Continuous ι := GlobalTheory.IsoMean.continuous_cplx V W B
  have hgc : ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (g G G') :=
    fun G G' hG hG' => ((GlobalTheory.T.continuous_isotropicSandwichMean_translation D V W a b P Q ψ hψ μ 𝓨 hμ' G hG).comp hιc).mul
      ((GlobalTheory.T.continuous_isotropicSandwichMean_translation D V W a b P Q ψ hψ μ 𝓨 hμ' G' hG').comp hιc).star
  have hgp : ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      ∀ γ ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ z, g G G' (γ + z) = g G G' z := by
    intro G G' hG hG' γ hγ z
    simp only [hg]
    rw [show ι (γ + z) = ι γ + ι z from GlobalTheory.IsoMean.cplx_add V W B γ z]
    exact GlobalTheory.IsoMean.meanX_mul_star_rat V W P Q μ 𝓨 ψ hψ G G' hG hG' (ι γ) (hιrat γ hγ) (horth γ) (ι z)
  have hχ1 : ∀ γ ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ψ (symplO V W (ι γ) (ι c)) = 1 :=
    fun γ hγ => (hsep γ).2 hγ
  have hchar : ∀ c z z', ψ (symplO V W (ι (z + z')) (ι c)) = ψ (symplO V W (ι z) (ι c)) * ψ (symplO V W (ι z') (ι c)) := by
    intro c z z'
    rw [show ι (z + z') = ι z + ι z' from GlobalTheory.IsoMean.cplx_add V W B z z', GlobalTheory.IsoMean.symplO_eq_add,
      GlobalTheory.IsoMean.symplO_eq_add, GlobalTheory.IsoMean.symplO_eq_add, l1, ← AddChar.map_add_eq_mul]
    exact congrArg ψ (by ring)
  have hchar2 : ∀ c c' z, ψ (symplO V W (ι z) (ι (c + c'))) = ψ (symplO V W (ι z) (ι c)) * ψ (symplO V W (ι z) (ι c')) := by
    intro c c' z
    rw [show ι (c + c') = ι c + ι c' from GlobalTheory.IsoMean.cplx_add V W B c c', GlobalTheory.IsoMean.symplO_eq_add,
      GlobalTheory.IsoMean.symplO_eq_add, GlobalTheory.IsoMean.symplO_eq_add, l2, ← AddChar.map_add_eq_mul]
    exact congrArg ψ (by ring)
  have hχc : ∀ c, Continuous fun z => ψ (symplO V W (ι z) (ι c)) := by
    intro c
    have h := (GlobalTheory.FinTranslate.continuous_symplOH V W (ι c)).comp hιc
    have e : (fun z => ψ (symplO V W (ι z) (ι c))) = fun z => ψ (symplOH V W (ι z) (ι c) + symplOH V W (ι z) (ι c)) := by
      funext z; rw [GlobalTheory.IsoMean.symplO_eq_add]
    rw [e]
    exact hψ.1.1.comp (h.add h)
  have hint : ∀ c ∈ GlobalTheory.MixModel.ratMx D 1 k, ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' →
      IntegrableOn (fun z => ψ (symplO V W (ι z) (ι c)) * g G G' z) 𝓩 η := by
    intro c hc G G' hG hG'
    refine GlobalTheory.MixModel.covolOne_integrableOn hη _ ((hχc c).mul (hgc G G' hG hG')) fun γ hγ z => ?_
    rw [hchar, hχ1 γ hγ c hc, one_mul, hgp G G' hG hG' γ hγ z]
  have key := GlobalTheory.T.eq_zero_of_coefficients_separatingCharacters_eq_zero (Mx D 1 k) (GlobalTheory.MixModel.ratMx D 1 k) K hK hKc (GlobalTheory.MixModel.ratMx D 1 k)
    (fun c z => ψ (symplO V W (ι z) (ι c))) (fun c => hχc c) (fun c z z' => hchar c z z')
    (fun c c' z => by exact hchar2 c c' z)
    (fun z => by
      show ψ (symplO V W (ι z) (ι 0)) = 1
      have h0 : symplOH V W (ι z) 0 = 0 := by
        have h := l2 (ι z) 0 0
        rw [add_zero] at h
        linear_combination -h
      rw [show ι 0 = 0 from GlobalTheory.IsoMean.cplx_zero V W B, GlobalTheory.IsoMean.symplO_eq_add, h0, add_zero,
        AddChar.map_zero_eq_one])
    (fun c z => hψ.1.2.1 _)
    (fun z => by rw [← hsep z]; exact Subtype.forall)
    η 𝓩 hη.1 hη.2.1 (fun z => g F₁ F₁' z - g F₂ F₂' z) ((hgc F₁ F₁' h₁ h₁').sub (hgc F₂ F₂' h₂ h₂'))
    (fun γ hγ z => by simp only [hgp F₁ F₁' h₁ h₁' γ hγ z, hgp F₂ F₂' h₂ h₂' γ hγ z])
    (fun c => by
      have e1 := hcoef c c.2 F₁ F₁' h₁ h₁'
      have e2 := hcoef c c.2 F₂ F₂' h₂ h₂'
      have e3 := H ν 𝓕 hν.1 hν2 (ι c) (horth c)
      rw [e1, e2] at e3
      have e4 := mul_left_cancel₀ hκ e3
      simp only [mul_sub]
      rw [integral_sub (hint c c.2 F₁ F₁' h₁ h₁') (hint c c.2 F₂ F₂' h₂ h₂')]
      exact sub_eq_zero.2 e4)
  have e := congrFun key 0
  simp only [Pi.zero_apply, hg] at e
  rw [show ι 0 = 0 from GlobalTheory.IsoMean.cplx_zero V W B] at e
  exact sub_eq_zero.1 e

end GlobalTheory.IsoMean

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
open scoped Classical

noncomputable section
namespace GlobalTheory.IdemCut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem smul_phi_of_mul_eq_zero {a e : AF F} (h : a * e = 0) (M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    a • phi e M = a • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
  simp only [phi, smul_add, smul_smul, mul_sub, mul_one, h, sub_zero, zero_smul, add_zero]

theorem smul_phi_of_mul_eq_self {a e : AF F} (h : a * e = a) (M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    a • phi e M = a • M := by
  simp only [phi, smul_add, smul_smul, mul_sub, mul_one, h, sub_self, zero_smul, zero_add]

theorem idempotentCut_latticeStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'), G.IsGood B →
    ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J, ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) (e : AF F) (he : e * e = e), S₁ ⊆ S →
      (∀ w ∉ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u * e = 0 ∨ u * e = u) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) ∧
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (GlobalTheory.FinDecomp.loc e he h))ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔
        γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) := by
  intro F E _ _ _ _ _ σ B a a' G hG h
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h) G.W.L hG.hW.lat
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h⁻¹) G.W.L hG.hW.lat
  refine ⟨S₁ ∪ S₂, fun S e he hS hcut => ?_⟩
  have key : ∀ w ∉ S, ∀ (X : ℕ) (Xs : Spc F E X), ∀ γ,
      γ * (mat (loc e he h))ᵀ ∈ latAtV Xs G.W w ↔ γ ∈ latAtV Xs G.W w := by
    intro w hw X Xs γ
    have hw1 : w ∉ S₁ := fun h' => hw (hS (Finset.mem_union_left _ h'))
    have hw2 : w ∉ S₂ := fun h' => hw (hS (Finset.mem_union_right _ h'))
    refine GlobalTheory.T.tensorLattice_mul_transpose_stable_iff F E X _ Xs G.W w _ _ (mat_inv_mul (loc e he h)) ?_ ?_ γ
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc]
      rcases hcut w hw u hu with h0 | h1
      · rw [smul_phi_of_mul_eq_zero h0, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact AddSubgroup.subset_closure ⟨u, hu, hint, y, hy, rfl⟩
      · rw [smul_phi_of_mul_eq_self h1, Matrix.smul_mulVec]
        exact hS₁ w hw1 u hu hint y hy
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc_inv]
      rcases hcut w hw u hu with h0 | h1
      · rw [smul_phi_of_mul_eq_zero h0, Matrix.smul_mulVec, Matrix.one_mulVec]
        exact AddSubgroup.subset_closure ⟨u, hu, hint, y, hy, rfl⟩
      · rw [smul_phi_of_mul_eq_self h1, Matrix.smul_mulVec]
        exact hS₂ w hw2 u hu hint y hy
  exact ⟨fun w hw => key w hw _ G.V, fun w hw => key w hw _ G.V'⟩

end GlobalTheory.IdemCut
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.discrete_series_spectral_side : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → HasDSComp M π := by
  first | exact @GlobalTheory.hasDSComp_of_trace_ne_zero | exact GlobalTheory.hasDSComp_of_trace_ne_zero | (intros; apply GlobalTheory.hasDSComp_of_trace_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.besselColumnScalarFunction_continuous_leftInvariant : Big fun ch => ∀ a, Continuous (colFn ch a) ∧
    ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g, colFn ch a (γ * g) = colFn ch a g := by
  first | exact @GlobalTheory.RowClaim.colFn_cont_left | exact GlobalTheory.RowClaim.colFn_cont_left | (intros; apply GlobalTheory.RowClaim.colFn_cont_left <;> assumption)
end

section

open GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.rowTestLiftFormula_principalLevel : StepProj → StepFlip → StepUnfold → StepJets → ConstK → SumOKK → Formula2K := by
  first | exact @GlobalTheory.RowClaim.FormulaTwo.formula2K | exact GlobalTheory.RowClaim.FormulaTwo.formula2K | (intros; apply GlobalTheory.RowClaim.FormulaTwo.formula2K <;> assumption)
end
