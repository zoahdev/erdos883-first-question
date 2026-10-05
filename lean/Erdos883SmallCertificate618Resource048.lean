import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_48 :
    (List.ofFn coreChunks618_48).flatten =
      (coreData618.take (coreResources618 48).q).drop 102 := by
  decide +kernel

theorem coreCheck618_48 :
    ∀ c : Fin 1, (coreChunks618_48 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 48)) = true := by
  decide +kernel
#print axioms coreFlatten618_48
#print axioms coreCheck618_48
end Erdos883Verified
