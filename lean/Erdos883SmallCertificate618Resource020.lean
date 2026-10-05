import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_20 :
    (List.ofFn coreChunks618_20).flatten =
      (coreData618.take (coreResources618 20).q).drop 130 := by
  decide +kernel

theorem coreCheck618_20 :
    ∀ c : Fin 1, (coreChunks618_20 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 20)) = true := by
  decide +kernel
#print axioms coreFlatten618_20
#print axioms coreCheck618_20
end Erdos883Verified
