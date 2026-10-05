import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_103 :
    (List.ofFn coreChunks618_103).flatten =
      (coreData618.take (coreResources618 103).q).drop 265 := by
  decide +kernel

theorem coreCheck618_103 :
    ∀ c : Fin 1, (coreChunks618_103 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 103)) = true := by
  decide +kernel
#print axioms coreFlatten618_103
#print axioms coreCheck618_103
end Erdos883Verified
