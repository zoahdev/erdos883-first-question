import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_39 :
    (List.ofFn coreChunks618_39).flatten =
      (coreData618.take (coreResources618 39).q).drop 81 := by
  decide +kernel

theorem coreCheck618_39 :
    ∀ c : Fin 1, (coreChunks618_39 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 39)) = true := by
  decide +kernel
#print axioms coreFlatten618_39
#print axioms coreCheck618_39
end Erdos883Verified
