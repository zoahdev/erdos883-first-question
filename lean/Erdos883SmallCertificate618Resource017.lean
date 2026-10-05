import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_17 :
    (List.ofFn coreChunks618_17).flatten =
      (coreData618.take (coreResources618 17).q).drop 125 := by
  decide +kernel

theorem coreCheck618_17 :
    ∀ c : Fin 1, (coreChunks618_17 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 17)) = true := by
  decide +kernel
#print axioms coreFlatten618_17
#print axioms coreCheck618_17
end Erdos883Verified
