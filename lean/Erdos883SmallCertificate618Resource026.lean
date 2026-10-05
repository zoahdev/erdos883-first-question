import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_26 :
    (List.ofFn coreChunks618_26).flatten =
      (coreData618.take (coreResources618 26).q).drop 137 := by
  decide +kernel

theorem coreCheck618_26 :
    ∀ c : Fin 1, (coreChunks618_26 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 26)) = true := by
  decide +kernel
#print axioms coreFlatten618_26
#print axioms coreCheck618_26
end Erdos883Verified
