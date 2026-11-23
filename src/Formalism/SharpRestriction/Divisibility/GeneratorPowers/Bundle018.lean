module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle014
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R') {d : ℕ}

def mp {n : ℕ} (a : Pt R n d) : Pt R' n d := fun i => map ψ (a i)

private theorem hs_lemma {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) :
    MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)

private theorem cz_ev_lemma_2 {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) (hf : constantCoeff f = 0) : constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hs_lemma a ha) (fun p => ha p.1 p.2) hf

theorem map_ev' {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R m d) :
    map ψ (ev a f) = ev (fun j => mp ψ (a j)) (map ψ f) := by
  unfold ev
  exact MvPowerSeries.map_subst (hs_lemma a ha) f

theorem mp_pt {n : ℕ} (j : Fin n) : mp ψ (pt R d j) = pt R' d j := by
  funext i
  simp only [mp, pt, MvPowerSeries.map_X]

theorem mp_zero {n : ℕ} : mp ψ (0 : Pt R n d) = 0 := by
  funext i
  simp [mp]

theorem mp_cons {n m : ℕ} (p : Pt R n d) (u : Fin m → Pt R n d) :
    (fun j => mp ψ (Matrix.vecCons p u j)) = Matrix.vecCons (mp ψ p) (fun j => mp ψ (u j)) := by
  funext j
  cases j using Fin.cases with
  | zero => rfl
  | succ k => rfl

theorem mp_nil {n : ℕ} : (fun j => mp ψ ((![] : Fin 0 → Pt R n d) j)) = ![] := by
  funext j
  exact j.elim0

theorem cz_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp only [pt, MvPowerSeries.constantCoeff_X]

theorem cz_add (F : Fin d → PS R 2 d) (hF : ∀ i, constantCoeff (F i) = 0) {n : ℕ} (a b : Pt R n d)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin d) :
    constantCoeff (addOf F a b i) = 0 := by
  have h : ∀ (j : Fin 2) (k : Fin d), constantCoeff ((![a, b] : Fin 2 → Pt R n d) j k) = 0 := by
    intro j k
    fin_cases j
    · exact ha k
    · exact hb k
  show constantCoeff (ev ![a, b] (F i)) = 0
  exact cz_ev_lemma_2 ![a, b] h (F i) (hF i)

theorem cz_comp1 (φ : Pt R 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0) {n : ℕ} (a : Pt R n d)
    (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) : constantCoeff (comp1 φ a i) = 0 := by
  have h : ∀ (j : Fin 1) (k : Fin d), constantCoeff ((![a] : Fin 1 → Pt R n d) j k) = 0 := by
    intro j k
    fin_cases j
    exact ha k
  show constantCoeff (ev ![a] (φ i)) = 0
  exact cz_ev_lemma_2 ![a] h (φ i) (hφ i)

theorem mp_add (F : Fin d → PS R 2 d) {n : ℕ} (a b : Pt R n d)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    mp ψ (addOf F a b) = addOf (fun i => map ψ (F i)) (mp ψ a) (mp ψ b) := by
  funext i
  have h : ∀ (j : Fin 2) (k : Fin d), constantCoeff ((![a, b] : Fin 2 → Pt R n d) j k) = 0 := by
    intro j k
    fin_cases j
    · exact ha k
    · exact hb k
  show MvPowerSeries.map ψ (ev ![a, b] (F i)) = ev ![mp ψ a, mp ψ b] (MvPowerSeries.map ψ (F i))
  rw [map_ev' ψ _ h]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem mp_comp1 (φ : Pt R 1 d) {n : ℕ} (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) :
    mp ψ (comp1 φ a) = comp1 (mp ψ φ) (mp ψ a) := by
  funext i
  have h : ∀ (j : Fin 1) (k : Fin d), constantCoeff ((![a] : Fin 1 → Pt R n d) j k) = 0 := by
    intro j k
    fin_cases j
    exact ha k
  show MvPowerSeries.map ψ (ev ![a] (φ i)) = ev ![mp ψ a] (MvPowerSeries.map ψ (φ i))
  rw [map_ev' ψ _ h]
  congr 1
  funext j
  fin_cases j
  rfl

def mapG (G : FGLaw R d) : FGLaw R' d where
  F := fun i => map ψ (G.F i)
  const := fun i => by rw [constantCoeff_map, G.const i, map_zero]
  unit := fun i => by
    have h := congrArg (map ψ) (G.unit i)
    rw [map_ev' ψ _ (by intro j k; fin_cases j <;> simp [cz_pt]), mp_cons, mp_cons, mp_nil, mp_zero, mp_pt,
      map_X] at h
    exact h
  comm := fun i => by
    have h := congrArg (map ψ) (G.comm i)
    rw [map_ev' ψ _ (by intro j k; fin_cases j <;> simp [cz_pt]), mp_cons, mp_cons, mp_nil, mp_pt, mp_pt] at h
    exact h
  assoc := fun i => by
    have h := G.assoc i
    change ev ![addOf G.F (pt R d 0) (pt R d 1), pt R d 2] (G.F i) =
      ev ![pt R d 0, addOf G.F (pt R d 1) (pt R d 2)] (G.F i) at h
    have h2 := congrArg (map ψ) h
    rw [map_ev' ψ _ (by intro j k; fin_cases j <;> simp [cz_pt, cz_add _ G.const]),
      map_ev' ψ _ (by intro j k; fin_cases j <;> simp [cz_pt, cz_add _ G.const]),
      mp_cons, mp_cons, mp_nil, mp_cons, mp_cons, mp_nil, mp_add ψ _ _ _ (cz_pt _) (cz_pt _),
      mp_add ψ _ _ _ (cz_pt _) (cz_pt _), mp_pt, mp_pt, mp_pt] at h2
    exact h2

def mapA {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) : OAct O (mapG ψ G) where
  act := fun a => mp ψ (A.act a)
  const := fun a i => by
    show constantCoeff (map ψ (A.act a i)) = 0
    rw [constantCoeff_map, A.const a i, map_zero]
  hom := fun a => by
    have h := congrArg (mp ψ) (A.hom a)
    simp only [FGLaw.add] at h
    rw [mp_comp1 ψ _ _ (cz_add _ G.const _ _ (cz_pt _) (cz_pt _)), mp_add ψ _ _ _ (cz_pt _) (cz_pt _),
      mp_add ψ _ _ _ (cz_comp1 _ (A.const a) _ (cz_pt _)) (cz_comp1 _ (A.const a) _ (cz_pt _)),
      mp_comp1 ψ _ _ (cz_pt _), mp_comp1 ψ _ _ (cz_pt _), mp_pt, mp_pt] at h
    exact h
  add_act := fun a b => by
    have h := congrArg (mp ψ) (A.add_act a b)
    simp only [FGLaw.add] at h
    rw [mp_add ψ _ _ _ (A.const a) (A.const b)] at h
    exact h
  mul_act := fun a b => by
    have h := congrArg (mp ψ) (A.mul_act a b)
    rw [mp_comp1 ψ _ _ (A.const b)] at h
    exact h
  one_act := by
    have h := congrArg (mp ψ) A.one_act
    rw [mp_pt] at h
    exact h

section FB

variable {O : Type} [CommRing O] [StarRing O] (B : FB R d O)

local macro "fbm" : tactic => `(tactic|
  (simp only [map_mul, map_one, FGLaw.add, map_ev', mp_cons, mp_nil, mp_pt, mp_zero,
    mp_add, mp_comp1, Fin.forall_fin_succ, IsEmpty.forall_iff, Matrix.cons_val_zero,
    Matrix.cons_val_succ, cz_pt, cz_add _ B.G.const, cz_comp1 _ (B.A.const _), map_zero,
    Pi.zero_apply, implies_true, and_self, forall_const, true_and] at *))


def mapFB : FB R' d O where
  G := mapG ψ B.G
  A := mapA ψ B.A
  ph1 := map ψ B.ph1
  ph2 := map ψ B.ph2
  sy := map ψ B.sy
  ad := fun a => map ψ (B.ad a)
  cocycleLeft_zero_fst := by have h := congrArg (map ψ) B.cocycleLeft_zero_fst; fbm; exact h
  cocycleLeft_zero_snd := by have h := congrArg (map ψ) B.cocycleLeft_zero_snd; fbm; exact h
  cocycleLeft_zero_thd := by have h := congrArg (map ψ) B.cocycleLeft_zero_thd; fbm; exact h
  cocycleRight_zero_fst := by have h := congrArg (map ψ) B.cocycleRight_zero_fst; fbm; exact h
  cocycleRight_zero_snd := by have h := congrArg (map ψ) B.cocycleRight_zero_snd; fbm; exact h
  cocycleRight_zero_thd := by have h := congrArg (map ψ) B.cocycleRight_zero_thd; fbm; exact h
  symmetry_zero_fst := by have h := congrArg (map ψ) B.symmetry_zero_fst; fbm; exact h
  symmetry_zero_snd := by have h := congrArg (map ψ) B.symmetry_zero_snd; fbm; exact h
  adjoint_zero_fst := fun a => by have h := congrArg (map ψ) (B.adjoint_zero_fst a); fbm; exact h
  adjoint_zero_snd := fun a => by have h := congrArg (map ψ) (B.adjoint_zero_snd a); fbm; exact h
  cocycleLeft_assoc := by have h := congrArg (map ψ) B.cocycleLeft_assoc; fbm; exact h
  cocycleLeft_comm := by have h := congrArg (map ψ) B.cocycleLeft_comm; fbm; exact h
  cocycleRight_assoc := by have h := congrArg (map ψ) B.cocycleRight_assoc; fbm; exact h
  cocycleRight_comm := by have h := congrArg (map ψ) B.cocycleRight_comm; fbm; exact h
  interchange := by have h := congrArg (map ψ) B.interchange; fbm; exact h
  sy_inv := by have h := congrArg (map ψ) B.sy_inv; fbm; exact h
  sy_law := by have h := congrArg (map ψ) B.sy_law; fbm; exact h
  adjoint_compat_left := fun a => by have h := congrArg (map ψ) (B.adjoint_compat_left a); fbm; exact h
  adjoint_compat_right := fun a => by have h := congrArg (map ψ) (B.adjoint_compat_right a); fbm; exact h
  ad_one := by show map ψ (B.ad 1) = 1; rw [B.ad_one, map_one]
  ad_mul := fun a b => by have h := congrArg (map ψ) (B.ad_mul a b); fbm; exact h
  ad_add := fun a b => by have h := congrArg (map ψ) (B.ad_add a b); fbm; exact h
  ad_sy := fun a => by have h := congrArg (map ψ) (B.ad_sy a); fbm; exact h

end FB

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBMap

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

theorem fbMap_holds : FBMapSt := by
  intro R R' _ _ ψ d O _ _ B
  exact ⟨FBMap.mapFB ψ B, fun j => rfl, fun a j => rfl, rfl, rfl, rfl, fun a => rfl⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def ChartJetTanSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (FT : Fin d → Germ.PS T.V 2 d) (actT : 𝓞 E → Fin d → Germ.PS T.V 1 d)
    (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d FT actT tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    letI := io.toAlgebra
    ∀ ℓ : Lt1 Dw, IsCombAt y.1.x
      (fun j : Fin d => (Formalism.L2.Pj.homAt y.1.x
        (jetTan ((0 : Fin 1), j) : Jet T.Fr (Fin 1 × Fin d) (0 + 1) →ₐ[T.Fr] DualNumber T.Fr) ≫ JetTr.xU I xT 1).left)
      (fun i => algebraMap T.V T.Fr (uvecT ℓ i)) (y.1.u ℓ.1 ℓ.2)

def ChartJetBasisSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (FT : Fin d → Germ.PS T.V 2 d) (actT : 𝓞 E → Fin d → Germ.PS T.V 1 d)
    (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d FT actT tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (Formalism.L2.Pj.homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    ∀ v : Fin d → T.Fr, ∃! a : Lt1 Dw → T.Fr, ∀ j, ∑ ℓ, a ℓ * algebraMap T.V T.Fr (uvecT ℓ j) = v j

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  Formalism.L2.Pj CIndFrFix

def FrTruncFixBSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y),
    ∃ (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1))
      (cc : ℕ → Fin C.d → Fin C.d → S),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } ∧ cc 0 = 0 ∧ (∀ m i j, cc m i j = cc m j i) ∧
      (∀ m (ℓ ℓ' : Lt1 Dw), ∑ i, ∑ j, cc m i j * C.uvec ℓ i * C.uvec ℓ' j ≠ 0 →
        ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) ∧
      ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
        (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m))

def HarmInvSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (cc : Fin C.d → Fin C.d → S), (∀ i j, cc i j = cc j i) →
    (∀ ℓ ℓ' : Lt1 Dw, ∑ i, ∑ j, cc i j * C.uvec ℓ i * C.uvec ℓ' j ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) →
    ∀ (k n D : ℕ) (f f' : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S),
    (∀ b, psJet D (f' b) = psJet D (f b * expP ((k : S) • diagL C.B H.w0 cc))) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      (∀ m ∈ P.support, m.degree ≤ D) → chartVal C k f' P = chartVal C k f P

theorem chartIndep2_verb (hTr : ChartIndepTruncSt) (hFix : FrTruncFixBSt) (hGerm : GermFixSt)
    (hInv : HarmInvSt) : ChartIndepSt2 := by
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C C' k n F f f' hf hf' a P hP

  have hD : ∀ m ∈ P.support, m.degree ≤ P.support.sup (fun m => m.degree) :=
    fun m hm => Finset.le_sup (f := fun m => m.degree) hm

  have step : ∀ (C₀ : ChartAt Xo c y) (f₀ : Fin n → MvPowerSeries (Fin 1 × Fin C₀.d) S),
      (∀ b, IsGerm y C₀.d C₀.x C₀.B.A.act C₀.e C₀.wP k (F b) (f₀ b)) →
      ∃ (C₁ : ChartAt Xo c y) (f₁ : Fin n → MvPowerSeries (Fin 1 × Fin C₁.d) S),
        FrTruncC y C₁ ∧ (∀ b, IsGerm y C₁.d C₁.x C₁.B.A.act C₁.e C₁.wP k (F b) (f₁ b)) ∧
        chartVal C₁ k f₁ P = chartVal C₀ k f₀ P := by
    intro C₀ f₀ hf₀
    obtain ⟨e', hfr, hrig, cc, hT1, -, hsym, hbal, hu⟩ := hFix E H Dw l Xo c hstar S y C₀
    choose f₁ hf₁ hj using fun b =>
      hGerm E H Dw l Xo c hstar S y C₀ e' hfr hrig cc hT1 hu k (F b) (f₀ b) (hf₀ b)
    exact ⟨{ C₀ with e := e', frame := hfr, rig0 := hrig }, f₁, hT1, hf₁,
      hInv E H Dw l Xo c hstar S y C₀ (cc (P.support.sup fun m => m.degree)) (hsym _) (hbal _) k n
        (P.support.sup fun m => m.degree) f₀ f₁ (fun b => hj b _) a P hP hD⟩
  obtain ⟨C₁, f₁, hC₁, hf₁, e₁⟩ := step C f hf
  obtain ⟨C₂, f₂, hC₂, hf₂, e₂⟩ := step C' f' hf'
  rw [← e₁, ← e₂]
  exact hTr E H Dw l Xo c hstar S y C₁ C₂ hC₁ hC₂ k n F f₁ f₂ hf₁ hf₂ a P hP

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.L2.Pj.SaturatedCharts (toT prodPts_of_combAt combAt_of_prodPts chartTan_of tanAt_of isTan_iff' fst_comp_jetTan)

attribute [local instance] Over.cartesianMonoidalCategory

section Lemmas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem isChartG_reindex (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) {κ κ' : Type}
    [Fintype κ] [Fintype κ'] (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (tg : κ → (Sp (DualNumber S) ⟶ t.G.left))
    (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (h : IsChartG t x0 d F act tg uvec x) (e : κ' ≃ κ) :
    IsChartG t x0 d F act (fun ℓ => tg (e ℓ)) (fun ℓ => uvec (e ℓ)) x := by
  refine ⟨h.zero, h.trunc, h.law, h.act, fun ℓ => h.tan (e ℓ), ?_⟩
  intro v
  obtain ⟨b, hb, hbu⟩ := h.basis v
  refine ⟨fun ℓ => b (e ℓ), fun j => ?_, fun a ha => ?_⟩
  · rw [← hb j]
    exact Equiv.sum_comp e (fun ℓ => b ℓ * uvec ℓ j)
  · have h1 : (fun ℓ => a (e.symm ℓ)) = b := hbu _ fun j => by
      rw [← ha j, ← Equiv.sum_comp e (fun ℓ => a (e.symm ℓ) * uvec ℓ j)]
      simp only [Equiv.symm_apply_apply]
    funext ℓ
    rw [← h1]
    simp only [Equiv.symm_apply_apply]

variable {V : Type} [CommRing V] (t : SAB H (Sp V))

theorem combAt_iff {n : ℕ} {x} (hx : ReciprocityTheory.ChartRestriction.G.Chart.IsUnivChart t.G n x) {m : ℕ}
    (f : Fin m → (Sp (DualNumber V) ⟶ t.G.left)) (hf : ∀ i, f i ≫ t.G.hom = spMap (algebraMap V (DualNumber V)))
    (hft : ∀ i, ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t (f i) (hf i))) (a : Fin m → V)
    (w : Sp (DualNumber V) ⟶ t.G.left) (hw : w ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) :
    IsCombAtG t (𝟙 (Sp V)) f a w ↔ ∃ h : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t w hw),
      ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx _ h = ∑ i, a i • ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx _ (hft i) := by
  constructor
  · intro hc
    have e := prodPts_of_combAt (t := t) f hf a w hw hc
    obtain ⟨h, hh⟩ := ReciprocityTheory.ChartRestriction.G.Chart.prodPts_tan hx a (fun i => toT t (f i) (hf i)) hft
    have hT : ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t w hw) := by rw [e]; exact h
    exact ⟨hT, (ReciprocityTheory.ChartRestriction.G.Chart.tcoord_congr hx e hT h).trans hh⟩
  · rintro ⟨h, hh⟩
    apply combAt_of_prodPts (t := t) f hf a w hw
    obtain ⟨h', hh'⟩ := ReciprocityTheory.ChartRestriction.G.Chart.prodPts_tan hx a (fun i => toT t (f i) (hf i)) hft
    exact ReciprocityTheory.ChartRestriction.G.Chart.tan_ext hx h h' (hh.trans hh'.symm)

theorem dir_tan {d : ℕ} (xc : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
    (hz : ∀ m, homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) m →ₐ[V] V) ≫ xc m = 1) (j : Fin d)
    (ho : (homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫
      xc 1).left ≫ t.G.hom = spMap (algebraMap V (DualNumber V))) :
    ReciprocityTheory.ChartRestriction.G.Chart.IsTan (toT t _ ho) := by
  apply chartTan_of
  refine ⟨ho.trans (Category.comp_id _).symm, ?_⟩
  have h1 := congrArg CommaMorphism.left (hz 1)
  simp only [Over.comp_left] at h1 ⊢
  have h2 : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫
      (homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V)).left =
      (homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V)).left := by
    show spMap _ ≫ spMap _ = spMap _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact congrArg (fun φ : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V => φ.toRingHom) (fst_comp_jetTan ((0 : Fin 1), j))
  rw [← Category.assoc, h2, h1]
  have hobj : spMap (algebraMap V V) ≫ 𝟙 (Sp V) = 𝟙 (Sp V) := by
    rw [Category.comp_id]
    first
      | (rw [Algebra.algebraMap_self]; exact Spec.map_id _)
      | simp [spMap]
  have h3 : ∀ (f g : Sp V ⟶ Sp V), f = g →
      (1 : Over.mk f ⟶ t.G).left = (1 : Over.mk g ⟶ t.G).left := by
    rintro f g rfl; rfl
  exact h3 _ _ hobj

end Lemmas

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Main

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
