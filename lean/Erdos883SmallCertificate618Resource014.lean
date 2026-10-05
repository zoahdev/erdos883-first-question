import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_14 :
    (List.ofFn coreChunks618_14).flatten =
      (coreData618.take (coreResources618 14).q).drop 121 := by
  decide +kernel

theorem coreCheck618_14 :
    ∀ c : Fin 1, (coreChunks618_14 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 14)) = true := by
  decide +kernel
#print axioms coreFlatten618_14
#print axioms coreCheck618_14
end Erdos883Verified
