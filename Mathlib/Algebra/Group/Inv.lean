/-
using results from the following sources
https://carleton.ca/math/wp-content/uploads/Cheaney-Kyle-Honours-Project-An_Introduction_to_Inverse_Semigroups.pdf
https://arxiv.org/pdf/2006.01628.pdf
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Ring.Idempotents


section InverseSemigroup

-- S is an inverse semigroup, if every element s in S has a unique inverse
class InverseSemigroup (S : Type*) extends Semigroup S, Inv S :=
  mul_inv_mul: ∀ (s : S), s = s * s⁻¹ * s
  inv_unique: ∀ (s t : S), s = s * t * s → t = s⁻¹
  inv_inv : ∀ (s : S), (s⁻¹)⁻¹ = s

variable {G:Type} [InverseSemigroup G]

theorem mul_inv_mul {s : G} : s = s * s⁻¹ * s :=
  InverseSemigroup.mul_inv_mul s

theorem unique_inv {s t : G} : s = s * t * s → t = s⁻¹ :=
  InverseSemigroup.inv_unique s t

theorem inv_inv₁ : ∀ (s : G), (s⁻¹)⁻¹ = s :=
  InverseSemigroup.inv_inv

/-
If e be an indempotent, Then e = e². So:
e = ee⁻¹e = (ee)e⁻¹(ee) = e(ee⁻¹e)e = eee
By the uniqueness of inverses, e = e⁻¹
-/
theorem inv_idem {s : G} (h: IsIdempotentElem s): s = s⁻¹ := by
  have triple : s = s*s*s := by rw [h, h]
  exact unique_inv triple

/-
Let S be an inverse semigroup. Then for all s ∈ S, ss−1 and s⁻¹s are idempotents.
Proof: Let S be a semigroup and let s ∈ S. Consider ss⁻¹ ∈ S. Then:
(ss⁻¹)²= (ss⁻¹)(ss⁻¹) = s (s⁻¹ss⁻¹) = ss⁻¹
-/
theorem idem_mul_inv {s : G} : IsIdempotentElem (s*s⁻¹) := by
  unfold IsIdempotentElem
  rw [← mul_assoc, ← mul_inv_mul]

theorem idem_inv_mul {s : G} : IsIdempotentElem (s⁻¹*s) := by
  unfold IsIdempotentElem
  rw [mul_assoc, ← mul_assoc s, ← mul_inv_mul]


/-
Proposition 2.2: A regular semigroup is inverse if and only if its idempotents commute.
Proof. Let S be a regular semigroup. Suppose its idempotents commute. Let s ∈ S and
assume u and v are inverses of s. That is, s = sus, u = usu and s = svs, v = vsv. Then,
u = u(svs)u = (us)(vs)u = (vs)(us)u = vs(usu) = (vsv)su = v(sv)(su) = v(su)(sv) = v(sus)v = vsv = v

Conversely, suppose S is a regular inverse semigroup. Let u, v ∈ E(S). We want to show that uv ∈ E(S).
Since S is regular, ∃s ∈ S such that uv = uvsuv
We note that: uv(vsu)uv = u(vv)s(uu)v = uvsuv

Since S is inverse, we have s = vsu
By definition of s, we have: s = suvs = (vsu)uv(vsu) = vs(uu)(vv)su = (vsu)(vsu) = (vsu)²
Thus, s = vsu ∈ E(S)
And since s ∈ E(S), =⇒ s = s⁻¹ = uv
=⇒ uv ∈ E(S)
This implies that E(S) is closed under multiplication.
=⇒ vu ∈ E(S)
Now consider:
(uv)(vu)(uv) = u(vv)(uu)v = (uv)(uv) = (uv)² = uv
=⇒ uv is an inverse of uv.
Since S in an inverse semigroup, inverses are unique.
=⇒ vu = uv
=⇒ idempotents commute.
-/
theorem idem_comm {u v : G} (hu : IsIdempotentElem u) (hv : IsIdempotentElem v): Commute u v := by
  -- Define the inverse of the product uv
  let s := (u * v)⁻¹
  have s_inv : s⁻¹ = u*v := by rw [inv_inv₁]
  -- Show that v * x * u is an idempotent inverse of uv
  have vsu_idem : IsIdempotentElem (v*s*u) := by {
    unfold IsIdempotentElem
    calc v * s * u * (v * s * u) = v * s * u * (v * s) * u := by rw [← mul_assoc]
     _ = v * (s* u * (v * s)) * u := by rw [mul_assoc v, mul_assoc v]
     _ = v * (s * (u * v) * s) * u := by rw [mul_assoc s, ← mul_assoc u, ← mul_assoc s]
    rw [← s_inv, ← mul_inv_mul]
  }
  -- Show that (uv)⁻¹ = v * s * u by uniqueness of inverses
  have uv_inv_unique : (u * v)⁻¹ = v * s * u := by {
    sorry
  }
  -- Show that (uv)⁻¹ is an idempotent
  have uv_inv_idem : IsIdempotentElem (u * v)⁻¹ := by {
    rw [uv_inv_unique]
    exact vsu_idem
  }
  -- Show that s is an idempotent
  have s_idem : IsIdempotentElem s := by {
    rw [← inv_inv₁ s, s_inv]
    exact uv_inv_idem
  }
  -- Show that uv is an idempotent
  have uv_idem : IsIdempotentElem (u*v) := by {
    sorry
  }
  -- Show that vu is an idempotent
  have vu_idem : IsIdempotentElem (v*u) := by {
    sorry
  }
    -- Show that uv and vu are inverses of uv
  have comm : u*v = v*u := by {
    have h1 : u*v = (u*v) * (v*u) * (u*v) := by {
          calc u*v = (u*v) * (u*v)⁻¹ * (u*v) := mul_inv_mul
          _ = (u*v) * (v*s*u) * (u*v) := by rw [uv_inv_unique]
          _ = (u*v) * (v*(u*v)*u) * (u*v) := by rw [inv_idem s_idem, s_inv]
          _ = (u*v) * (v*u) * (u*v) := by rw [← mul_assoc v, mul_assoc (v*u), vu_idem]
    }
    rw [unique_inv h1]
    exact inv_idem uv_idem
  }
  exact comm

end InverseSemigroup
