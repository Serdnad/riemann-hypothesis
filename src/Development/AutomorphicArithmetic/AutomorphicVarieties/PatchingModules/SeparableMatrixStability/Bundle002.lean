module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Mathlib.NumberTheory.Padics.RingHoms
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle004
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

section

noncomputable section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

def DD.map {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] (g : ℕ) (f : X →ₐ[A] X') :
    DD X g →ₐ[A] DD X' g where
  toFun x := ⟨f x.a, fun j => f (x.ep j), fun j => f (x.ep' j), f x.eta⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  commutes' a := by
    show _ = DD.C (algebraMap A X' a)
    have : algebraMap A (DD X g) a = DD.C (algebraMap A X a) := rfl
    rw [this]
    ext <;> simp

section

variable {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] (g : ℕ) (f : X →ₐ[A] X')
  (x : DD X g)

@[simp] theorem DD.map_a : (DD.map g f x).a = f x.a := rfl
@[simp] theorem DD.map_ep (j) : (DD.map g f x).ep j = f (x.ep j) := rfl
@[simp] theorem DD.map_ep' (j) : (DD.map g f x).ep' j = f (x.ep' j) := rfl
@[simp] theorem DD.map_eta : (DD.map g f x).eta = f x.eta := rfl

instance [Finite X] : Finite (DD X g) := Finite.of_equiv _ (DD.equiv (X := X) (g := g)).symm

end

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n)

abbrev NP.redD (g m : ℕ) : DD x.A g →ₐ[x.A] DD (x.Am m) g := DD.map g (Ideal.Quotient.mkₐ x.A _)

def NP.UnipOn (H : Subgroup F.Γ) : Prop :=
  ∀ (m : ℕ) (h : F.G₀), (h : F.Γ) ∈ H → ∃ e : ℕ, ∀ i j, (mat x.ρ (h ^ l ^ e) - 1) i j ∈ Ideal.span {x.t ^ m}

end UpperTheory.V.Pa
end
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem comm_of_sep {K V : Type} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f g h : Module.End K V) (hs : f.charpoly.Separable)
    (hg : Commute f g) (hh : Commute f h) : g * h = h * g := by
  classical
  have key : ∀ μ : K, ∀ x ∈ f.maxGenEigenspace μ, (g * h) x = (h * g) x := by
    intro μ x hx
    have hd : Module.finrank K (f.maxGenEigenspace μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_le_one_of_separable hs μ
    obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hd
    have hgW := Module.End.mapsTo_maxGenEigenspace_of_comm hg μ
    have hhW := Module.End.mapsTo_maxGenEigenspace_of_comm hh μ
    obtain ⟨a, ha⟩ := hv ⟨x, hx⟩
    obtain ⟨b, hb⟩ := hv ⟨g (v : V), hgW v.2⟩
    obtain ⟨c, hc⟩ := hv ⟨h (v : V), hhW v.2⟩
    have ha' : a • (v : V) = x := congrArg Subtype.val ha
    have hb' : b • (v : V) = g v := congrArg Subtype.val hb
    have hc' : c • (v : V) = h v := congrArg Subtype.val hc
    rw [← ha', Module.End.mul_apply, Module.End.mul_apply, map_smul, map_smul, map_smul, map_smul,
      ← hb', ← hc', map_smul, map_smul, ← hb', ← hc', smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hker : ∀ μ, f.maxGenEigenspace μ ≤ LinearMap.ker (g * h - h * g) := by
    intro μ x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact key μ x hx
  have htop : LinearMap.ker (g * h - h * g) = ⊤ := by
    rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top f]
    exact iSup_le hker
  exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp htop)

private theorem mat_comm_of_sep {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (P Z E : Matrix (Fin n) (Fin n) K) (hs : P.charpoly.Separable)
    (hg : P * Z = Z * P) (hh : P * E = E * P) : Z * E = E * Z := by
  let φ := (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K))
  have hc : (φ P).charpoly = P.charpoly := Matrix.charpoly_toLin' P
  have e := comm_of_sep (φ P) (φ Z) (φ E) (by rw [hc]; exact hs)
    (by rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hg])
    (by rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hh])
  apply φ.injective
  rw [map_mul, map_mul]
  exact e

theorem UpperTheory.V.Pa.od_comm :
    ∀ (A : Type) [CommRing A] [IsDomain A] (n a : ℕ) (P Z : Matrix (Fin n) (Fin n) A) (al : Fin n → A), P ∈ Ev A A n a → Z ∈ Od A A n a → Function.Injective al → P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) → P * Z = Z * P → Z = 0 := by
  intro A _ _ n a P Z al hP hZ hal hchar hPZ
  classical
  have hP' : ∀ i j : Fin n, ¬((i : ℕ) < a ↔ (j : ℕ) < a) → P i j = 0 := by
    intro i j h
    have := (hP i j).2 h
    simpa using this
  have hZ' : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j = 0 := by
    intro i j h
    have := (hZ i j).1 h
    simpa using this
  let e : Fin n → A := fun i => if (i : ℕ) < a then 1 else 0
  have hPE : P * Matrix.diagonal e = Matrix.diagonal e * P := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · simp [e, hi, hj]
    · simp [e, hi, hj, hP' i j (by simp [hi, hj])]
    · simp [e, hi, hj, hP' i j (by simp [hi, hj])]
    · simp [e, hi, hj]
  let K := AlgebraicClosure (FractionRing A)
  let ι : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hι : Function.Injective ι :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  have hs : (P.map ι).charpoly.Separable := by
    rw [Matrix.charpoly_map, hchar, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr (hι.comp hal)
  have h1 : P.map ι * Z.map ι = Z.map ι * P.map ι := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hPZ]
  have h2 : P.map ι * (Matrix.diagonal e).map ι = (Matrix.diagonal e).map ι * P.map ι := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hPE]
  have h3 := mat_comm_of_sep (P.map ι) (Z.map ι) ((Matrix.diagonal e).map ι) hs h1 h2
  rw [← Matrix.map_mul, ← Matrix.map_mul] at h3
  have h4 : Z * Matrix.diagonal e = Matrix.diagonal e * Z := Matrix.map_injective hι h3
  ext i j
  have h5 := congrFun (congrFun h4 i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h5
  rw [Matrix.zero_apply]
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
  · exact hZ' i j (by simp [hi, hj])
  · simp only [e, hi, hj, ↓reduceIte, mul_one, mul_zero, one_mul, zero_mul] at h5
    exact h5.symm
  · simp only [e, hi, hj, ↓reduceIte, mul_one, mul_zero, one_mul, zero_mul] at h5
    exact h5
  · exact hZ' i j (by simp [hi, hj])
end

section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem pl_le_ker {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ)
    (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (h1 : ∀ a ∈ H, PadicInt.toZMod ((ε a : ℤ_[l]ˣ) : ℤ_[l]) = 1) :
    PL l H ≤ ε.ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have key : ∀ k : ℕ, PadicInt.toZModPow k ((ε x : ℤ_[l])) = 1 := by
    intro k
    let χ : Γ →* (ZMod (l ^ k))ˣ :=
      (Units.map (PadicInt.toZModPow k : ℤ_[l] →+* ZMod (l ^ k)).toMonoidHom).comp ε
    have hmemχ : ∀ g, g ∈ χ.ker ↔
        (ε g : ℤ_[l]) ∈ Metric.closedBall (1 : ℤ_[l]) ((l : ℝ) ^ (-(k : ℤ))) := by
      intro g
      rw [MonoidHom.mem_ker, Metric.mem_closedBall, dist_eq_norm,
        PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
        map_one, sub_eq_zero, Units.ext_iff]
      rfl
    have hopen : IsOpen (χ.ker : Set Γ) := by
      have hset : (χ.ker : Set Γ) =
          (fun g => (ε g : ℤ_[l])) ⁻¹' Metric.closedBall 1 ((l : ℝ) ^ (-(k : ℤ))) := by
        ext g
        exact hmemχ g
      rw [hset]
      exact (IsUltrametricDist.isOpen_closedBall _
        (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero))).preimage
        (Units.continuous_val.comp hε)
    let U : OpenNormalSubgroup Γ := ⟨⟨χ.ker, hopen⟩, χ.normal_ker⟩
    have hcond : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U := by
      intro h hh
      refine ⟨k, ?_⟩
      show h ^ l ^ k ∈ χ.ker
      rw [hmemχ, map_pow, Units.val_pow_eq_pow_val, Metric.mem_closedBall, dist_eq_norm,
        PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
      have hd : (l : ℤ_[l]) ∣ (ε h : ℤ_[l]) - 1 := by
        rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
          RingHom.mem_ker, map_sub, map_one, h1 h hh, sub_self]
      have hp := dvd_sub_pow_of_dvd_sub hd k
      rw [one_pow] at hp
      exact (pow_dvd_pow _ (Nat.le_succ k)).trans hp
    have hle : PL l H ≤ (U.toOpenSubgroup : Subgroup Γ) := by
      unfold PL
      exact (iInf_le _ U).trans (iInf_le _ hcond)
    have hxU : x ∈ χ.ker := hle hx
    rw [MonoidHom.mem_ker] at hxU
    have hv := congrArg Units.val hxU
    simpa [χ] using hv
  exact Units.ext (PadicInt.ext_of_toZModPow.mp (fun k => by rw [key k, Units.val_one, map_one]))

theorem UpperTheory.V.Pa.quot_ex :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G : Glob l L) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (∀ a ∈ H, PadicInt.toZMod ((G.ε a : ℤ_[l]ˣ) : ℤ_[l]) = 1) → ∃ (G' : Glob l L) (g : G.Hom G'), g.p.ker = PL l H := by
  intro l _ L G H _ hH hη hε1
  have hN : (PL l H).Normal := by
    constructor
    intro x hx g
    simp only [PL, Subgroup.mem_iInf] at hx ⊢
    intro U hU
    exact U.isNormal'.conj_mem _ (hx U hU) g
  have hC : IsClosed (PL l H : Set G.Γ) := by
    simp only [PL, Subgroup.coe_iInf]
    exact isClosed_iInter fun U => isClosed_iInter fun _ => U.toOpenSubgroup.isClosed
  have hKH : PL l H ≤ H := by
    let U : OpenNormalSubgroup G.Γ := ⟨⟨H, hH⟩, inferInstance⟩
    have hcond : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U := by
      intro h hh
      refine ⟨0, ?_⟩
      change h ^ l ^ 0 ∈ H
      simpa using hh
    exact (iInf_le _ U).trans (iInf_le _ hcond)
  haveI := hN
  let π : G.Γ →* G.Γ ⧸ PL l H := QuotientGroup.mk' (PL l H)
  have hπc : Continuous π := QuotientGroup.continuous_mk
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπo : IsOpenMap π := QuotientGroup.isOpenMap_coe
  have hπq : Topology.IsQuotientMap π := hπo.isQuotientMap hπc hπs
  haveI : TotallyDisconnectedSpace (G.Γ ⧸ PL l H) := (totallyDisconnected_quot G.Γ _ hC).1
  let η' : G.Γ ⧸ PL l H →* ℤˣ := QuotientGroup.lift (PL l H) G.η (hKH.trans hη)
  let ε' : G.Γ ⧸ PL l H →* ℤ_[l]ˣ :=
    QuotientGroup.lift (PL l H) G.ε (pl_le_ker H G.ε G.ε_cont hε1)
  have hηo : IsOpen (η'.ker : Set (G.Γ ⧸ PL l H)) := by
    have hset : (η'.ker : Set (G.Γ ⧸ PL l H)) = π '' (G.η.ker : Set G.Γ) := by
      ext y
      obtain ⟨x, rfl⟩ := hπs y
      constructor
      · intro hy
        exact ⟨x, hy, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        show η' (π x) = 1
        rw [← hzx]
        exact hz
    rw [hset]
    exact hπo _ G.η_open
  have hεc : Continuous ε' := by
    rw [hπq.continuous_iff]
    exact G.ε_cont
  let r : G.η.ker →* η'.ker :=
    (π.comp G.η.ker.subtype).codRestrict η'.ker (fun x => by
      show η' (π x) = 1
      exact x.2)
  have hrc : Continuous r := continuous_induced_rng.2 (hπc.comp continuous_subtype_val)
  let G' : Glob l L :=
    { Γ := G.Γ ⧸ PL l H
      η := η'
      η_open := hηo
      c := π G.c
      c_sq := by rw [← map_mul, G.c_sq, map_one]
      η_c := G.η_c
      ε := ε'
      ε_cont := hεc
      φ := fun v => r.comp (G.φ v)
      φ_cont := fun v => hrc.comp (G.φ_cont v)
      φu := fun u => r.comp (G.φu u)
      φu_cont := fun u => hrc.comp (G.φu_cont u) }
  refine ⟨G', ⟨π, hπc, hπs, fun _ => rfl, rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, ?_⟩
  exact QuotientGroup.ker_mk' _
end
