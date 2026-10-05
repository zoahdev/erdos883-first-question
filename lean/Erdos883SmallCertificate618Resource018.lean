import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_18 :
    (List.ofFn coreChunks618_18).flatten =
      (coreData618.take (coreResources618 18).q).drop 126 := by
  decide +kernel

theorem coreCheck618_18 :
    ∀ c : Fin 1, (coreChunks618_18 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 18)) = true := by
  decide +kernel
#print axioms coreFlatten618_18
#print axioms coreCheck618_18
end Erdos883Verified
