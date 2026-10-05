import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_82 :
    (List.ofFn coreChunks618_82).flatten =
      (coreData618.take (coreResources618 82).q).drop 162 := by
  decide +kernel

theorem coreCheck618_82 :
    ∀ c : Fin 1, (coreChunks618_82 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 82)) = true := by
  decide +kernel
#print axioms coreFlatten618_82
#print axioms coreCheck618_82
end Erdos883Verified
