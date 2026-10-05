import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_100 :
    (List.ofFn coreChunks618_100).flatten =
      (coreData618.take (coreResources618 100).q).drop 256 := by
  decide +kernel

theorem coreCheck618_100 :
    ∀ c : Fin 1, (coreChunks618_100 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 100)) = true := by
  decide +kernel
#print axioms coreFlatten618_100
#print axioms coreCheck618_100
end Erdos883Verified
