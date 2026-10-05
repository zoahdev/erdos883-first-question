import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_15 :
    (List.ofFn coreChunks618_15).flatten =
      (coreData618.take (coreResources618 15).q).drop 123 := by
  decide +kernel

theorem coreCheck618_15 :
    ∀ c : Fin 1, (coreChunks618_15 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 15)) = true := by
  decide +kernel
#print axioms coreFlatten618_15
#print axioms coreCheck618_15
end Erdos883Verified
