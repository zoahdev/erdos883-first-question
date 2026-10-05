import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_33 :
    (List.ofFn coreChunks618_33).flatten =
      (coreData618.take (coreResources618 33).q).drop 149 := by
  decide +kernel

theorem coreCheck618_33 :
    ∀ c : Fin 1, (coreChunks618_33 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 33)) = true := by
  decide +kernel
#print axioms coreFlatten618_33
#print axioms coreCheck618_33
end Erdos883Verified
