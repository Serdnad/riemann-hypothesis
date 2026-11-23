module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CliffPrime
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle040
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
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
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

section

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Pr

section Nice

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {R : Type} [CommRing R]

structure Nice (ρ : NRep F n R) (p : Ideal R) : Prop where
  prime : p.IsPrime
  dim : qdim p = 1
  char : (l : R) ∈ p
  off : ρ.OffTri p
  sep : ∀ v i j, i ≠ j → ¬ ρ.Coin p v i j

def ThickLink [IsLocalRing R] (ρ : NRep F 3 R) (p q : Ideal R) : Prop :=
  Nice ρ p ∧ ρ.TE p ∧ Nice ρ q ∧ ρ.TE q ∧ ∃ e : Ideal R, e.IsPrime ∧ Thick ρ e ∧ e ≤ p ∧ e ≤ q

end Nice

section Input

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}

def P1' (S : Space O F n) (M : Ideal S.B) : Prop :=
  ∀ (x : Ideal S.A) (L : S.Loc x) (p : Ideal L.R), Nice L.ρ p → L.ρ.TI p → M ≤ L.π p →
    ∀ P : Ideal L.R, P.IsPrime → P ≤ p → M ≤ L.π P

def P23' (S : Space O F 3) (M : Ideal S.B) : Prop :=
  ∀ (x : Ideal S.A) (L : S.Loc x) (p q : Ideal L.R), Nice L.ρ p → L.ρ.TE p → Relation.ReflTransGen (ThickLink L.ρ) p q →
    (∃ P : Ideal L.R, P.IsPrime ∧ P ≤ p ∧ L.ρ.TI P ∧ M ≤ L.π P) →
    ∀ P' : Ideal L.R, P'.IsPrime → P' ≤ q → L.ρ.TI P' → M ≤ L.π P'

def SeedIn (S : Space O F n) (M : Ideal S.B) : Prop :=
  ∃ (ξ : Ideal S.A) (Z : Ideal S.B), ξ.IsPrime ∧ S.u.TI ξ ∧ Z.IsPrime ∧ M ≤ Z ∧ Z ≤ S.π ξ ∧
    qdim Z = ((1 + n * F.d : ℕ) : WithBot ℕ∞)

def AllGood (S : Space O F n) (M : Ideal S.B) : Prop := ∀ p : Ideal S.A, p.IsPrime → S.u.TI p → M ≤ S.π p

def OffFin (S : Space O F n) : Prop := ∃ I : Ideal S.B, S.FinLam I ∧ ∀ p : Ideal S.A, p.IsPrime → S.u.OffTri p → I ≤ S.π p

end Input

def PropagationTheoremGL2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → F.Big C₀ → ∀ (S : Space O F 2) (M : Ideal S.B),
    S.FinLam M → P1' S M → SeedIn S M → AllGood S M

def PropagationTheoremGL3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → F.Big C₀ → ∀ (S₂ : Space O F 2) (M₂ : Ideal S₂.B),
    S₂.FinLam M₂ → AllGood S₂ M₂ → ∀ (S : Space O F 3) (M : Ideal S.B),
    S.FinLam M → P1' S M → P23' S M → SeedIn S M → AllGood S M ∧ OffFin S

section Points

variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}

structure IsLiftA {A : Type} [CommRing A] [IsLocalRing A] [Algebra O A] [IsLocalHom (algebraMap O A)]
    (ρ : NRep F n A) : Prop where
  cont : ρ.Cont (maximalIdeal A)
  bar : (ρ.map (residue A)).IsBar (ResidueField.map (algebraMap O A))
  diag : (ρ.map (residue A)).IsDiag


variable (F n) in
def FinPt : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra O A] [IsCD O A] [Algebra (ResidueField O) A] [IsScalarTower O (ResidueField O) A]
    (ρ : NRep F n A), IsLiftA O ρ → (∀ v i, ∀ g ∈ F.Iv v, F.Ψ (F.loc v g) = 1 → ρ.ψ v i g = 1) →
    ∀ g, (ρ.r g).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (algebraMap (ResidueField O) A ((F.Ψ g ^ w n i : (ResidueField O)ˣ) : ResidueField O)))

end Points

def FinPtOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → ∀ S : Space O F 3, OffFin S → FinPt O F 3

section Link

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  (F : Frame l (ResidueField O)) {n : ℕ} {G : W.GFrame l} (r : W.Resid G O n)

structure TwLink where
  π : G.G₀ →* F.G0
  π_cont : Continuous π
  π_surj : Function.Surjective π
  π_conj : ∀ g, π (G.conj g) = F.conj (π g)
  π_eps : ∀ g : G.G₀, F.eps (π g) = G.ε g
  e : G.Vl ≃ F.V
  lam : ∀ v, G.Gv v ≃ₜ* F.Gv (e v)
  lam_loc : ∀ v g, F.loc0 (e v) (lam v g) = π (G.φ v g)
  lam_I : ∀ v g, lam v g ∈ F.Iv (e v) ↔ g ∈ G.Iv v
  κ : G.G₀ →* Oˣ
  κ_cont : AdicCont (maximalIdeal O) fun g => (κ g : O)
  κ_conj : ∀ g, κ g * κ (G.conj g) = G.eps O O g ^ (1 - (n : ℤ))
  chib : ∀ i g, r.chib i g = F.Ψ (π g) ^ w n i * W.pushCh (residue O) κ g
  psib : ∀ v i g, r.psib v i g = r.chib i (G.φ v g)
  mu : ∀ v, G.mu v ≤ (commutator (G.Gv v)).topologicalClosure
  tame : ∀ u, ∀ g ∈ G.Iu u, ∃ m : ℕ, ¬ l ∣ m ∧ π g ^ m = 1 ∧ κ g ^ m = 1
  ramκ : ∀ g ∈ G.I0, κ g = 1
  ker : ∀ N : Subgroup G.G₀, N.Normal → IsClosed (N : Set G.G₀) → (∀ g ∈ N, G.conj g ∈ N) →
    (∀ u, ∀ g ∈ G.Iu u, F.Ψ (π g) = 1 → g ∈ N) → G.I0 ≤ N → π.ker ≤ N

namespace TwLink

variable {F r} (K : TwLink F r) {A : Type} [CommRing A] [Algebra O A]

def κA (A : Type) [CommRing A] [Algebra O A] : G.G₀ →* Aˣ := W.pushCh (algebraMap O A) K.κ

def tw (ρ : NRep F n A) : G.G₀ →* Matrix (Fin n) (Fin n) A where
  toFun g := ((K.κA A g : Aˣ) : A) • ρ.r (K.π g)
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

def twψ (ρ : NRep F n A) (v : G.Vl) (i : Fin n) : G.Gv v →* Aˣ :=
  (ρ.ψ (K.e v) i).comp (K.lam v).toMulEquiv.toMonoidHom * (K.κA A).comp (G.φ v)

def IsPhi (B : W.UniversalOrdinaryDeterminantRing r) (S : Space O F n) (Φ : B.B →ₐ[O] S.B) : Prop :=
  B.u.Maps ((S.B.val.comp Φ : B.B →ₐ[O] S.R) : B.B →+* S.R) (W.GDet.ofRep (K.tw S.ρ)) (K.twψ S.ρ)

end TwLink

end Link

end UpperTheory.V.Pr

end
end

section

open Matrix Polynomial UpperTheory.V.U3 UpperTheory.V.Alg

private theorem ext_integral {B S K : Type} [CommRing B] [CommRing S] [Field K] [IsAlgClosed K] [Algebra B S]
    [Algebra.IsIntegral B S] (hinj : Function.Injective (algebraMap B S)) (φ : B →+* K) :
    ∃ Φ : S →+* K, ∀ b, Φ (algebraMap B S b) = φ b :=
  _root_.UpperTheory.Reformulated.B.Qe16.ext_integral hinj φ

private theorem charpoly_of_basis {κ : Type} [Field κ] {n : ℕ} (M : Matrix (Fin n) (Fin n) κ)
    (b : Module.Basis (Fin n) κ (Fin n → κ)) (a : Fin n → κ) (h : ∀ i, M *ᵥ b i = a i • b i) :
    M.charpoly = ∏ i, (X - C (a i)) := by
  rw [← Matrix.charpoly_toLin', ← LinearMap.charpoly_toMatrix _ b, ← Matrix.charpoly_diagonal]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, h, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Finsupp.single_apply, Ne.symm hij]

private theorem reduce_roots {κ k B : Type} [Field κ] [Field k] [CommRing B] (j : B →+* κ)
    (hj : Function.Injective j) (φ : B →+* k) :
    ∃ (S : Subring κ) (Φ : S →+* AlgebraicClosure k), ∀ (n : ℕ) (p : B[X]) (a : Fin n → κ),
      p.map j = ∏ i, (X - C (a i)) → ∃ h : ∀ i, a i ∈ S,
        (p.map φ).map (algebraMap k (AlgebraicClosure k)) = ∏ i, (X - C (Φ ⟨a i, h i⟩)) := by
  letI : Algebra B κ := j.toAlgebra
  have hinj : Function.Injective (algebraMap B (integralClosure B κ)) := by
    intro x y hxy
    exact hj (congrArg Subtype.val hxy)
  obtain ⟨Φ, hΦ⟩ := ext_integral hinj ((algebraMap k (AlgebraicClosure k)).comp φ)
  refine ⟨(integralClosure B κ).toSubring, Φ, fun n p a hp => ?_⟩
  have hm : p.Monic := by
    apply Polynomial.monic_of_injective hj
    rw [hp]
    exact monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have h : ∀ i, a i ∈ integralClosure B κ := fun i => by
    refine ⟨p, hm, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map]
    change (p.map j).eval _ = 0
    rw [hp, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  refine ⟨h, ?_⟩
  have h1 : p.map (algebraMap B (integralClosure B κ)) = ∏ i, (X - C (⟨a i, h i⟩ : integralClosure B κ)) := by
    apply Polynomial.map_injective (integralClosure B κ).val.toRingHom Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    exact hp
  have h2 := congrArg (Polynomial.map Φ) h1
  rw [Polynomial.map_map, Polynomial.map_prod] at h2
  simp only [Polynomial.map_sub, map_X, map_C] at h2
  rw [Polynomial.map_map]
  refine Eq.trans ?_ h2
  congr 1
  exact RingHom.ext fun b => (hΦ b).symm

theorem UpperTheory.V.Pr.irrNormal :
    UpperTheory.V.Pr.IrrNormal := by
  intro G κ k B _ _ _ _ _ n hn r hr j φ χ hj hred D _ ι ψ hψ U _ hdist hχ
  rcases UpperTheory.V.Pr.cliffPrime G κ n hn r hr U with h | h | ⟨b, la, π, -, hla, hπ, htr⟩
  · exact h
  · exfalso
    have h2 := hn.two_le
    obtain ⟨g, hg, hne⟩ := hdist ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
    obtain ⟨c, hc⟩ := h _ hg
    have hall : ∀ a, ((ψ a g : κˣ) : κ) = c := fun a => by
      have h1 := hψ g
      rw [hc, Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal] at h1
      have h3 := congrArg (Polynomial.eval ((ψ a g : κˣ) : κ)) h1
      rw [UpperTheory.V.Pr.chPoly, eval_prod, eval_prod,
        Finset.prod_eq_zero (f := fun i => eval ((ψ a g : κˣ) : κ) (X - C ((ψ i g : κˣ) : κ)))
          (Finset.mem_univ a) (by simp), Finset.prod_eq_zero_iff] at h3
      obtain ⟨_, _, h4⟩ := h3
      simpa [sub_eq_zero] using h4
    exact hne (Units.ext ((hall _).trans (hall _).symm))
  exfalso
  choose c hc using hπ
  have hb : ∀ i (x y : κ), x • b i = y • b i → x = y := fun i x y h =>
    smul_left_injective κ (b.ne_zero i) h
  have c1 : ∀ i, c 1 i = 1 := fun i => by
    have := hc 1 i
    simp only [UpperTheory.V.Pr.gm, map_one, Units.val_one, Matrix.one_mulVec, Equiv.Perm.coe_one, id] at this
    exact hb i _ _ (by rw [← this, one_smul])
  have cmul : ∀ g h i, c (g * h) i = c g (π h i) * c h i := fun g h i => by
    have := hc (g * h) i
    simp only [UpperTheory.V.Pr.gm, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec] at this
    rw [hc h i, Matrix.mulVec_smul, hc g, smul_smul] at this
    rw [mul_comm]
    exact (hb _ _ _ this).symm
  have cne : ∀ g i, c g i ≠ 0 := fun g i h0 => by
    have := cmul g⁻¹ g i
    rw [inv_mul_cancel, c1, h0, mul_zero] at this
    exact one_ne_zero this
  have cconj : ∀ g h i, π h = 1 → c (g * h * g⁻¹) (π g i) = c h i := fun g h i hh => by
    have e1 := cmul (g * h * g⁻¹) g i
    rw [inv_mul_cancel_right, cmul, hh] at e1
    apply mul_right_cancel₀ (cne g i)
    rw [← e1, mul_comm]; rfl
  have hU : ∀ u ∈ U, π u = 1 := fun u hu => by
    ext i
    by_contra hne
    have e := (hla i ⟨u, hu⟩).symm.trans (hc u i)
    have e2 := congrArg (fun v => b.repr v (π u i)) e
    have hne' : i ≠ π u i := fun h => hne (by rw [← h]; rfl)
    simp [Finsupp.single_apply, hne'] at e2
    exact cne u i e2.symm
  let kap : Fin n → π.ker →* κ := fun i =>
    { toFun := fun h => c h i
      map_one' := c1 i
      map_mul' := fun g h => by
        have := cmul g h i
        rw [(MonoidHom.mem_ker.1 h.2)] at this
        exact this }
  have hchar : ∀ h, π h = 1 → (UpperTheory.V.Pr.gm r h).charpoly = ∏ i, (X - C (c h i)) := fun h hh =>
    charpoly_of_basis _ b _ fun i => by rw [hc, hh]; rfl

  have hD : ∀ d, π (ι d) = 1 := by
    let e : U.comap ι →* π.ker :=
      (ι.comp (U.comap ι).subtype).codRestrict π.ker fun u => hU _ u.2
    obtain ⟨σ, hσ⟩ := UpperTheory.V.Pr.charPerm (U.comap ι) κ n (fun i => (ψ i).comp (U.comap ι).subtype)
      (fun i => ((kap i).comp e).toHomUnits) (fun u => by
        have := hψ u
        rw [hchar _ (hU _ u.2)] at this
        exact this.symm)
    have hσ' : ∀ i u, ι u ∈ U → c (ι u) i = (ψ (σ i) u : κˣ) := fun i u hu => by
      have := congrArg Units.val (DFunLike.congr_fun (hσ i) (⟨u, hu⟩ : U.comap ι))
      exact this
    intro d
    refine Equiv.ext fun i => ?_
    by_contra hne
    obtain ⟨u, hu, hne'⟩ := hdist (σ (π (ι d) i)) (σ i) (fun h => hne (σ.injective h))
    apply hne'
    have e1 := cconj (ι d) (ι u) i (hU _ hu)
    have hu' : ι (d * u * d⁻¹) ∈ U := by
      rw [map_mul, map_mul, map_inv]; exact Subgroup.Normal.conj_mem _ hu _
    rw [← map_inv, ← map_mul, ← map_mul, hσ' _ _ hu', hσ' _ _ hu, map_mul, map_mul, map_inv,
      mul_inv_cancel_comm] at e1
    exact Units.ext e1
  obtain ⟨S, Φ, hS⟩ := reduce_roots j hj φ
  let t : kˣ →* (AlgebraicClosure k)ˣ := Units.map (algebraMap k (AlgebraicClosure k)).toMonoidHom
  have ht : Function.Injective t := Units.map_injective (algebraMap k (AlgebraicClosure k)).injective
  have key : ∀ h, π h = 1 → ∃ hh : ∀ i, c h i ∈ S,
      UpperTheory.V.Pr.chPoly (fun i => t.comp (χ i)) h = ∏ i, (X - C (Φ ⟨c h i, hh i⟩)) := fun h hh => by
    obtain ⟨p, hp1, hp2⟩ := hred h
    obtain ⟨hm, hq⟩ := hS n p _ (hp1.trans (hchar h hh))
    refine ⟨hm, ?_⟩
    rw [← hq, hp2, UpperTheory.V.Pr.chPoly, UpperTheory.V.Pr.chPoly, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    rfl
  choose hmem hkey using key
  let kb : Fin n → π.ker →* AlgebraicClosure k := fun i =>
    Φ.toMonoidHom.comp ((kap i).codRestrict S fun h => hmem h h.2 i)
  obtain ⟨τ, hτ⟩ := UpperTheory.V.Pr.charPerm π.ker (AlgebraicClosure k) n
    (fun i => (t.comp (χ i)).comp π.ker.subtype) (fun i => (kb i).toHomUnits) (fun h => hkey h h.2)
  have hτ' : ∀ i h (hh : π h = 1), Φ ⟨c h i, hmem h hh i⟩ = (t (χ (τ i) h) : (AlgebraicClosure k)ˣ) :=
    fun i h hh => by
      have := congrArg Units.val (DFunLike.congr_fun (hτ i) (⟨h, hh⟩ : π.ker))
      exact this
  obtain ⟨a, a', d, hne⟩ := hχ
  obtain ⟨g, hg⟩ := htr (τ.symm a') (τ.symm a)
  apply hne
  apply ht
  apply Units.ext
  have hc' : π (g * ι d * g⁻¹) = 1 := by rw [map_mul, map_mul, hD, mul_one, map_inv, mul_inv_cancel]
  have e1 := hτ' (τ.symm a) _ hc'
  have e2 := hτ' (τ.symm a') _ (hD d)
  rw [Equiv.apply_symm_apply] at e1 e2
  rw [map_mul (χ a), map_mul (χ a), map_inv (χ a), mul_inv_cancel_comm] at e1
  rw [← e1, ← e2]
  congr 1
  apply Subtype.ext
  show c _ _ = c _ _
  rw [← hg]
  exact cconj _ _ _ (hD d)
end
