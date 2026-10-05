import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_12 :
    (List.ofFn coreChunks618_12).flatten =
      (coreData618.take (coreResources618 12).q).drop 119 := by
  decide +kernel

theorem coreCheck618_12 :
    ∀ c : Fin 1, (coreChunks618_12 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 12)) = true := by
  decide +kernel
#print axioms coreFlatten618_12
#print axioms coreCheck618_12
end Erdos883Verified
