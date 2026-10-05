import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_10 :
    (List.ofFn coreChunks618_10).flatten =
      (coreData618.take (coreResources618 10).q).drop 116 := by
  decide +kernel

theorem coreCheck618_10 :
    ∀ c : Fin 1, (coreChunks618_10 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 10)) = true := by
  decide +kernel
#print axioms coreFlatten618_10
#print axioms coreCheck618_10
end Erdos883Verified
