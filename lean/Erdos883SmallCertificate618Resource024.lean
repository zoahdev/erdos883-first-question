import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_24 :
    (List.ofFn coreChunks618_24).flatten =
      (coreData618.take (coreResources618 24).q).drop 135 := by
  decide +kernel

theorem coreCheck618_24 :
    ∀ c : Fin 1, (coreChunks618_24 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 24)) = true := by
  decide +kernel
#print axioms coreFlatten618_24
#print axioms coreCheck618_24
end Erdos883Verified
