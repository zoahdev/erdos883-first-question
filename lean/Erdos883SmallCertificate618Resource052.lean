import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_52 :
    (List.ofFn coreChunks618_52).flatten =
      (coreData618.take (coreResources618 52).q).drop 107 := by
  decide +kernel

theorem coreCheck618_52 :
    ∀ c : Fin 1, (coreChunks618_52 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 52)) = true := by
  decide +kernel
#print axioms coreFlatten618_52
#print axioms coreCheck618_52
end Erdos883Verified
