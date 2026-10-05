import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_22 :
    (List.ofFn coreChunks618_22).flatten =
      (coreData618.take (coreResources618 22).q).drop 133 := by
  decide +kernel

theorem coreCheck618_22 :
    ∀ c : Fin 1, (coreChunks618_22 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 22)) = true := by
  decide +kernel
#print axioms coreFlatten618_22
#print axioms coreCheck618_22
end Erdos883Verified
