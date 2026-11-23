module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle634
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle332
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle633
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle627
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle635
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

open GlobalTheory.StdFrames


namespace GlobalTheory.RowMoveAt
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem notOff (S : GridChoice W U) {t : T} (ht : t ∈ U) {w : Pl D.host.E} (hw : w ∈ locPl G t) : ¬ Off S.N.S w := by
  classical
  intro h0
  have h3 := S.N.off w h0
  rcases Finset.mem_union.1 hw with h | h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    exact h3.1 (by rw [G.pl.under_w hv]; exact hv)
  · exact h3.2.1 t ht w h rfl

theorem cpt_supp_zero {S : Finset ℕ} {w : Pl D.host.E} (hw : ¬ Off S w) {P : Finset (Pl D.host.E)} {e : AE D}
    (he : IsIdemSum e P) (hoff : ∀ w' ∈ P, Off S w') : cpt w (toEAf D (e + cA D e)) = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he

  rw [map_sum, ← Finset.sum_add_distrib, map_sum, map_sum]
  refine Finset.sum_eq_zero fun w' hw' => ?_
  obtain ⟨hne, hnc⟩ := GlobalTheory.StdHalfLat.ne_and_not_conj hw (hoff w' hw')
  rw [map_add (f := _), map_add (f := _), (cpt_of_isIdemAt (hes w' hw')).2 w hne,
    (cpt_of_isIdemAt (GlobalTheory.MovedIdem.isIdemAt_conj (hes w' hw') (GlobalTheory.IdemSupport.mem_cP w'))).2 w ?_, add_zero]
  rintro rfl
  apply hnc
  intro c hc
  exact ⟨GlobalTheory.IdemSupport.cO D c, (GlobalTheory.IdemSupport.mem_cP w' c).1 hc, by simp [GlobalTheory.IdemSupport.cO]⟩

theorem map_mt_eq_one {S : Finset ℕ} {w : Pl D.host.E} (hw : ¬ Off S w) {P : Finset (Pl D.host.E)} {e : AE D}
    (he : IsIdemSum e P) (hoff : ∀ w' ∈ P, Off S w') {V : HSp D} {g : GA D V} (hg : SuppAt e V g) :
    (mt V g).map ((cpt w).comp (toEAf D)) = 1 := by
  have h0 := cpt_supp_zero hw he hoff
  have h1 : (mt V g - 1).map ((cpt w).comp (toEAf D)) = 0 := by
    ext i j
    rw [Matrix.map_apply, ← hg i j, RingHom.comp_apply, map_mul, map_mul, h0, zero_mul, Matrix.zero_apply]
  have h2 : (mt V g).map ((cpt w).comp (toEAf D)) =
      (mt V g - 1).map ((cpt w).comp (toEAf D)) + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map ((cpt w).comp (toEAf D)) := by
    rw [← Matrix.map_add _ (map_add _), sub_add_cancel]
  rw [h2, h1, zero_add, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.RowMoveAt

namespace GlobalTheory.RowMoveAt
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem actO_chi_right (j : ℕ) (M : GA D (G.V (.grid (j + 1) D.R.m)))
    (x : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))) :
    actO _ _ (G.toPair (.chi j D.R.m) 1 M)⁻¹.1 (G.toPair (.chi j D.R.m) 1 M)⁻¹.2 x =
      (x : Matrix _ _ (AE D)) * mt (G.V (.grid (j + 1) D.R.m)) M := by
  simp only [actO, GridData.toPair, Prod.fst_inv, Prod.snd_inv, inv_inv, inv_one]
  rw [show mt (G.pT (.chi j D.R.m : Pair T)) 1 = 1 from rfl, Matrix.one_mul]
  rfl

theorem actO_chi_left (j : ℕ) (M : GA D (G.V (.grid (j + 1) D.R.m)))
    (x : WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) :
    actO _ _ (G.toPair (.chi (j + 1) D.R.m) M 1)⁻¹.1 (G.toPair (.chi (j + 1) D.R.m) M 1)⁻¹.2 x =
      mt (G.V (.grid (j + 1) D.R.m)) M⁻¹ * (x : Matrix _ _ (AE D)) := by
  simp only [actO, GridData.toPair, Prod.fst_inv, Prod.snd_inv, inv_inv, map_one, inv_one]
  rw [show mt (G.pS (.chi (j + 1) D.R.m : Pair T)) 1 = 1 from rfl, Matrix.mul_one]

theorem sub_mul_cast {K : Type} [Field K] {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (Y : Matrix (Fin a) (Fin b) K) (X : Matrix (Fin b) (Fin b) K) :
    ((P⁻¹).val * (Y * X) * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) =
      ((P⁻¹).val * Y * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) * ((Q⁻¹).val * X * Q.val).submatrix (Fin.cast hb) (Fin.cast hb) := by
  rw [← Matrix.submatrix_mul _ _ (Fin.cast ha) (Fin.cast hb) (Fin.cast hb) (finCongr hb).bijective]
  congr 1
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]

theorem mul_sub_cast {K : Type} [Field K] {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (Y : Matrix (Fin a) (Fin b) K) (X : Matrix (Fin a) (Fin a) K) :
    ((P⁻¹).val * (X * Y) * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) =
      ((P⁻¹).val * X * P.val).submatrix (Fin.cast ha) (Fin.cast ha) * ((P⁻¹).val * Y * Q.val).submatrix (Fin.cast ha) (Fin.cast hb) := by
  rw [← Matrix.submatrix_mul _ _ (Fin.cast ha) (Fin.cast ha) (Fin.cast hb) (finCongr ha).bijective]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P.val), Units.mul_inv, Matrix.one_mul]

theorem inBasis_val {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) :
    (inBasis h β w x).val = (((loc w β)⁻¹).val * (loc w x).val * (loc w β).val).submatrix (Fin.cast h) (Fin.cast h) := by
  ext i j
  rw [GlobalTheory.FunObj.ProdOpen.inBasis_apply, ← map_inv, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
  rfl

end GlobalTheory.RowMoveAt

namespace GlobalTheory.RowMoveAt

theorem rowAt_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (w : Pl D.host.E), w ∈ locPl G t →
    ∀ (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    S.rowAt t w (Function.update (Function.update y ⟨j, by omega⟩
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
          (y ⟨j, by omega⟩) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
      ⟨j + 1, hj⟩ (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
          (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (y ⟨j + 1, hj⟩) :
          WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)))) =
    Function.update (Function.update (S.rowAt t w y) j
        (S.rowAt t w y j * @id (Matrix (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m)))
            (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m))) (Kw w)) (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
          (finG (G.V (.grid (j + 1) D.R.m)) k)).val))
      (j + 1) (@id (Matrix (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m)))
            (Fin ((locGrid G t w).rank (j + 1, (locGrid G t w).m))) (Kw w)) (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w
          (finG (G.V (.grid (j + 1) D.R.m)) k))⁻¹.val * S.rowAt t w y (j + 1)) := by
  intro D T L sc G W U S t ht j hj k w hw y
  have hX : DefNode D.R.m (.grid (j + 1) D.R.m) := ⟨by omega, rfl⟩
  obtain ⟨P, e, he, hsupp, hoff⟩ := S.N.u_supp _ hX
  have hn := notOff S ht hw
  have hu := map_mt_eq_one hn he hoff hsupp
  have hu' := map_mt_eq_one hn he hoff (GlobalTheory.StdHalfLat.suppAt_inv' hsupp)
  have hM : (mt _ (moved S j k)).map ((cpt w).comp (toEAf D)) = (loc w (finG (G.V (.grid (j + 1) D.R.m)) k)).val := by
    rw [show mt _ (moved S j k) = mt _ (S.N.u (.grid (j + 1) D.R.m)).1⁻¹ * mt _ k.1 * mt _ (S.N.u (.grid (j + 1) D.R.m)).1 from rfl,
      Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]
    rfl
  have hM' : (mt _ (moved S j k)⁻¹).map ((cpt w).comp (toEAf D)) = (loc w (finG (G.V (.grid (j + 1) D.R.m)) k⁻¹)).val := by
    rw [show mt _ (moved S j k)⁻¹ = mt _ (S.N.u (.grid (j + 1) D.R.m)).1⁻¹ * mt _ k.1⁻¹ * mt _ (S.N.u (.grid (j + 1) D.R.m)).1 from by
      rw [RowVertexInv.moved]; simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]; rfl,
      Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]
    rfl
  funext i

  by_cases h1 : i = j + 1
  · subst h1
    rw [Function.update_self]
    simp only [GridChoice.rowAt, dif_pos hj, Function.update_self, Frames.coord]
    rw [actO_chi_left, Matrix.map_mul, hM']
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose, id_eq]
    rw [← map_inv (inBasis _ (S.B.β (j + 1) D.R.m) w), map_inv (finG (G.V (Node.grid (j + 1) D.R.m))) k, inBasis_val, mul_sub_cast]
    rfl
  by_cases h2 : i = j
  · subst h2
    rw [Function.update_of_ne (by omega), Function.update_self]
    have hj' : i < D.R.m := by omega
    simp only [GridChoice.rowAt, dif_pos hj', Frames.coord]
    rw [Function.update_of_ne (fun h => by simp [Fin.ext_iff] at h), Function.update_self, actO_chi_right, Matrix.map_mul, hM]
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose, id_eq]
    rw [inBasis_val, sub_mul_cast]
    rfl
  · rw [Function.update_of_ne h1, Function.update_of_ne h2]
    simp only [GridChoice.rowAt]
    by_cases hi : i < D.R.m
    · rw [dif_pos hi, dif_pos hi, Function.update_of_ne (fun h => h1 (by simpa [Fin.ext_iff] using h)),
        Function.update_of_ne (fun h => h2 (by simpa [Fin.ext_iff] using h))]
    · rw [dite_eq_right hi, dite_eq_right hi]
end GlobalTheory.RowMoveAt
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

noncomputable section

namespace GlobalTheory.GfCArch

def infIncl (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun a := ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  map_add' a b := by
    show ((a + b, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) + ((b, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp
  map_smul' c a := by
    show ((c • a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = c • ((a, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
    simp

theorem smul_eq_zero_of_fst (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : AF F ⊗[F] E) (hx : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x = 0) (u : AF F)
    (hu : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u) : u • x = 0 := by
  let e : AF F := ((1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  let f : AF F := ((0, 1) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
  have hf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F f = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0
    exact map_zero _
  have h0 : f • u = 0 := hu f hf
  have hef : e + f = 1 := by
    refine Prod.ext ?_ ?_
    · show (1 : Ainf F) + 0 = 1
      rw [add_zero]
    · show (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) + 1 = 1
      rw [zero_add]
  have hu' : u = e * u := by
    calc u = (e + f) * u := by rw [hef, one_mul]
      _ = e * u + f • u := add_mul _ _ _
      _ = e * u := by rw [h0, add_zero]
  have key : ∀ y : AF F ⊗[F] E,
      e • y = (infIncl F).rTensor E (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      congr 1
      show ((1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) * (show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a) =
        (((show Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F from a).1, 0) : Ainf F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)
      refine Prod.ext ?_ ?_
      · exact one_mul _
      · exact zero_mul _
    | add y z hy hz => rw [smul_add, hy, hz, map_add (f := _), map_add (f := _)]
  rw [hu', mul_comm, mul_smul, key, hx, map_zero, smul_zero]

theorem gfc_arch : ∀ (D : D7) (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X), g ∈ GfC X →
    ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u →
      u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (σ := D.sp.cm.sig) (GlobalTheory.TripleRead.toUX X e hJ g) - 1) = 0 := by
  intro D X k e J hJ g hg u hu
  have hM : ∀ a b, Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.L2.Theta.mt X g - 1) a b) = 0 :=
    (GlobalTheory.FinPl.KOpen.mem_GfC_iff X g).1 hg
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (σ := D.sp.cm.sig) (GlobalTheory.TripleRead.toUX X e hJ g) - 1 = (Formalism.L2.Theta.mt X g - 1).submatrix e e := by
    show (Formalism.L2.Theta.mt X g).submatrix e e - 1 = _
    ext i j
    simp [Matrix.one_apply, e.injective.eq_iff]
  rw [hr]
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply, Matrix.submatrix_apply]
  exact smul_eq_zero_of_fst _ _ _ (hM _ _) u hu

end GlobalTheory.GfCArch

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type}

theorem passesThrough_of_canFlip {x : ℕ × ℕ} {r : List (ℕ × ℕ)} :
    ∀ (l : List (ℕ × ℕ)) (γ : List GlobalTheory.SplitFlip.Edge), GlobalTheory.SplitFlip.CanFlip γ (l ++ x :: r) →
      GlobalTheory.SplitFlip.PassesThrough x.1 x.2 (l.foldl (fun γ y => GlobalTheory.SplitFlip.flipPath y.1 y.2 γ) γ)
  | [], γ, h => by cases h with | cons hp _ => exact hp
  | y :: l, γ, h => by
    cases h with
    | cons _ hc => exact passesThrough_of_canFlip l _ hc

theorem lt_of_mem_flipOrder {m : ℕ} {x : ℕ × ℕ} (h : x ∈ flipOrder m) : x.1 < m ∧ x.2 < m := by
  simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, j, hj, rfl⟩ := h
  exact ⟨hi, hj⟩

theorem prod_map_range {M : Type*} [CommMonoid M] (f : ℕ → M) : ∀ n, ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.prod_append, prod_map_range f n, Finset.prod_range_succ]; simp

theorem prod_flipOrder {M : Type*} [CommMonoid M] (m : ℕ) (f : ℕ × ℕ → M) :
    ((flipOrder m).map f).prod = ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m, f (i, j) := by
  have : ∀ l : List ℕ, ((l.flatMap fun i => (List.range m).map fun j => (i, j)).map f).prod =
      (l.map fun i => ((List.range m).map fun j => f (i, j)).prod).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih, List.map_map, Function.comp_def]
  rw [flipOrder, this, prod_map_range]
  exact Finset.prod_congr rfl fun i _ => prod_map_range _ _

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}



theorem flipAt_of (hL : R.toLevCh.Is A.μ0) (ch : Choice R)
    (hA : ∀ (t : T) (i j : Fin D.R.m), CommutesWith ch.W ch.S.B ch.rm t i j (ch.c i j t))
    (hB : ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t)
    (hC : ∀ (t : T) (y : (R.HX t).H), GlobalTheory.FlipRun.IsCuspListed ch.W.θ (.grid 0 D.R.m) (GlobalTheory.RowClaim.formTop ch t y))
    (hD : ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum,
        ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m),
          GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧
          ∀ M : Vol ch.G, M.Is t → ∀ y,
            TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧
            thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) =
              (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y))
    (hE : ∀ (t : T) (Φ : ch.G.Datum), ∀ w ∈ locPl ch.G t, ∀ k, k ≤ D.R.m ^ 2 →
      (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w)
        ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).path
        ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).tensor)
    (hK : ∀ i j (t : T), ch.c i j t ≠ 0) : FlipAt ch := by
  obtain ⟨Pg, hPg⟩ := hD
  choose z hz hPg using hPg
  refine ⟨(GlobalTheory.FlipRun.flipsPolE ch.rm (flipOrder D.R.m) Pg).mapDomain GlobalTheory.FlipRun.toOpp, z, fun t => ⟨hz t, fun Φ => ?_⟩⟩
  obtain ⟨τg, hRg, hg⟩ := hPg t Φ
  let c' : ℕ × ℕ → ℂ := fun x => if h : x.1 < D.R.m ∧ x.2 < D.R.m then ch.c ⟨x.1, h.1⟩ ⟨x.2, h.2⟩ t else 1
  let S : ℕ → ∀ w, (locGrid ch.G t w).PiLocalization₂ := fun k w =>
    (givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)
  have hlev : ∀ k w, (S k w).level = givenLevel ch.G t w := fun k w =>
    flips_level _ _ _ _ _ _ fun _ _ => rfl
  have hpath : ∀ k w, (S k w).path =
      ((flipOrder D.R.m).take k).foldl (fun γ x => GlobalTheory.SplitFlip.flipPath x.1 x.2 γ) (GlobalTheory.SplitFlip.givenPath D.R.m) := fun k w =>
    flips_path _ _ _ _ _ _
  have hlen : (flipOrder D.R.m).length = D.R.m ^ 2 := (canFlip_flipOrder D.R.m).2.1
  have key : ∀ k, k ≤ D.R.m ^ 2 → ∃ p : Path T (.grid 0 D.R.m) (.grid D.R.m 0), GlobalTheory.FlipRun.OnGrid D.R.m t p ∧
      GlobalTheory.FlipRun.edges p = ((flipOrder D.R.m).take k).foldl (fun γ x => GlobalTheory.SplitFlip.flipPath x.1 x.2 γ)
        (GlobalTheory.SplitFlip.givenPath D.R.m) ∧
      ∃ τ : TotT ch.G p, GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t p τ (fun w => (S k w).tensor) ∧
        ∀ M : Vol ch.G, M.Is t → ∀ y,
          TotConv ch.W M p (GlobalTheory.FlipRun.tensE ch.W p (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg) τ)
            (GlobalTheory.RowClaim.formTop ch t y) ∧
          thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = ((z t : ℂ) * (((flipOrder D.R.m).take k).map c').prod)⁻¹ •
            liftT ch.W M p (GlobalTheory.FlipRun.tensE ch.W p (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg) τ)
              (GlobalTheory.RowClaim.formTop ch t y) := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨⟨h1, h2⟩, -, -⟩ := GlobalTheory.T.given_opposite_gridPaths_and_determined_by_edges D.R.m t
      refine ⟨GlobalTheory.FunObj.givenPath t D.R.m, h1, by simpa using h2, τg, hRg, fun M hM y => ?_⟩
      obtain ⟨a, b⟩ := hg M hM y
      refine ⟨a, ?_⟩
      simpa [GlobalTheory.FlipRun.flipsPolE] using b
    | succ k ih =>
      intro hk
      obtain ⟨p, hp, hedge, τ, hR, hI⟩ := ih (by omega)
      have hkl : k < (flipOrder D.R.m).length := by omega
      set x := (flipOrder D.R.m)[k] with hx
      have hxm : x ∈ flipOrder D.R.m := List.getElem_mem hkl
      obtain ⟨hi, hj⟩ := lt_of_mem_flipOrder hxm
      have htake : (flipOrder D.R.m).take (k + 1) = (flipOrder D.R.m).take k ++ [x] := List.take_succ_eq_append_getElem hkl
      have hpass : GlobalTheory.SplitFlip.PassesThrough x.1 x.2 (GlobalTheory.FlipRun.edges p) := by
        rw [hedge]
        have hc := (canFlip_flipOrder D.R.m).1
        rw [← List.take_append_drop k (flipOrder D.R.m), List.drop_eq_getElem_cons hkl] at hc
        exact passesThrough_of_canFlip _ _ hc
      obtain ⟨A, Bp, rfl, hA', hB', hN, hNe⟩ := GlobalTheory.T.gridPath_cut_at_square_swap_route D.R.m t x.1 x.2 hi hj p hp hpass
      have hT : ∀ w ∈ locPl ch.G t, (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w)
          (GlobalTheory.FlipRun.edges ((A.comp (routeSmall t x.1 x.2)).comp Bp)) (S k w).tensor := fun w hw => by
        have := hE t Φ w hw k (by omega)
        rwa [hpath, ← hedge] at this
      have hS : ∀ w, (S (k + 1) w).tensor = (locGrid ch.G t w).flipTensor .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w)
          x.1 x.2 (givenLevel ch.G t w) (S k w).tensor := fun w => by
        rw [← hlev k w]
        show ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take (k + 1))).tensor = _
        rw [htake]
        simp only [GlobalTheory.SplitFlip.Grid.PiLocalization₂.flips, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      have hTb : ∀ w ∈ locPl ch.G t, (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w)
          (GlobalTheory.FlipRun.edges ((A.comp (routeBig t x.1 x.2)).comp Bp))
          ((locGrid ch.G t w).flipTensor .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) x.1 x.2 (givenLevel ch.G t w)
            (S k w).tensor) := fun w hw => by
        have := hE t Φ w hw (k + 1) hk
        rw [← hS w, hNe, hedge]
        have e2 := hpath (k + 1) w
        rw [htake, List.foldl_append] at e2
        have e3 : (S (k + 1) w).path = GlobalTheory.SplitFlip.flipPath x.1 x.2
            (((flipOrder D.R.m).take k).foldl (fun γ x => GlobalTheory.SplitFlip.flipPath x.1 x.2 γ) (GlobalTheory.SplitFlip.givenPath D.R.m)) := e2
        rw [← e3]
        exact this
      obtain ⟨τ', hR', hF⟩ := GlobalTheory.T.gridSquareFlip_smallRoute_eq_inv_smul_bigRoute hL ch.W ch.S.B ch.rm t x.1 x.2 hi hj _ (hK _ _ t) (hA t ⟨x.1, hi⟩ ⟨x.2, hj⟩)
        A Bp hA' hB' (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg) τ (fun w => (S k w).tensor) hT hTb hR
      refine ⟨(A.comp (routeBig t x.1 x.2)).comp Bp, hN, ?_, τ', ?_, fun M hM y => ?_⟩
      · rw [hNe, hedge, htake, List.foldl_append]; rfl
      · have e : (fun w => (S (k + 1) w).tensor) = fun w => (locGrid ch.G t w).flipTensor .one (psiAt ch.W w) (unifAt w)
            (depthAt ch.G w) x.1 x.2 (givenLevel ch.G t w) (S k w).tensor := funext hS
        rw [e]; exact hR'
      · obtain ⟨hc1, hc2⟩ := hI M hM y
        obtain ⟨hn1, hn2⟩ := hF M hM (hB t M hM) _ (hC t y) hc1
        have ep : GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take (k + 1)) Pg =
            GlobalTheory.FlipRun.flipPolE ch.rm x.1 x.2 (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg) := by
          rw [htake, GlobalTheory.FlipRun.flipsPolE, GlobalTheory.FlipRun.flipsPolE, List.foldl_append]; rfl
        have ec : c' x = ch.c ⟨x.1, hi⟩ ⟨x.2, hj⟩ t := dif_pos ⟨hi, hj⟩
        rw [ep]
        refine ⟨hn1, ?_⟩
        rw [hc2, hn2, smul_smul, htake, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, ec]
        congr 1
        exact (mul_inv _ _).symm.trans (by rw [mul_assoc])
  obtain ⟨p, hp, hedge, τ, hR, hI⟩ := key (D.R.m ^ 2) le_rfl
  have htk : (flipOrder D.R.m).take (D.R.m ^ 2) = flipOrder D.R.m := List.take_of_length_le (by rw [hlen])
  obtain ⟨-, ⟨h1, h2⟩, h3⟩ := GlobalTheory.T.given_opposite_gridPaths_and_determined_by_edges D.R.m t
  have hp' : p = oppPath t D.R.m := h3 p _ hp h1 (by rw [hedge, h2, htk]; exact (canFlip_flipOrder D.R.m).2.2)
  subst hp'
  have hTf : (fun w => (S (D.R.m ^ 2) w).tensor) = Tflip ch.W ch.S.B t Φ := by
    funext w
    show ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take (D.R.m ^ 2))).tensor = _
    rw [htk]; rfl
  rw [hTf] at hR
  obtain ⟨τ', hτ', heq⟩ := GlobalTheory.T.flippedFiniteTensor_of_representing_oppositePath ch.W ch.S.B ch.rm t Φ (GlobalTheory.FlipRun.flipsPolE ch.rm (flipOrder D.R.m) Pg) τ hR
  have hprod : ((flipOrder D.R.m).map c').prod = cTot ch t := by
    rw [prod_flipOrder, cTot, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_range]
    exact Finset.prod_congr rfl fun j _ => dif_pos ⟨i.2, j.2⟩
  refine ⟨τ', hτ', fun M hM y => ?_⟩
  obtain ⟨hc1, hc2⟩ := hI M hM y
  rw [htk, heq] at hc1 hc2
  rw [hprod] at hc2
  exact ⟨hc1, hc2⟩

end GlobalTheory.FlipRun


end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.isWeilDatum_complexConjugate_of_negHermitianSpace : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep S T), GlobalTheory.Grid.IsWeil ψ true S T χS χT ω → IsWeilDatumO ψ S T χS⁻¹ χT⁻¹ (GlobalTheory.AdjTr.conjRep ω) := by
  first | exact @GlobalTheory.ConjWeilBack.weil_conjRep_of_neg | exact GlobalTheory.ConjWeilBack.weil_conjRep_of_neg | (intros; apply GlobalTheory.ConjWeilBack.weil_conjRep_of_neg <;> assumption)
end
