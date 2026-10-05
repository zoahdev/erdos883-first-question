import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_23 :
    (List.ofFn coreChunks618_23).flatten =
      (coreData618.take (coreResources618 23).q).drop 134 := by
  decide +kernel

theorem coreCheck618_23 :
    ∀ c : Fin 1, (coreChunks618_23 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 23)) = true := by
  decide +kernel
#print axioms coreFlatten618_23
#print axioms coreCheck618_23
end Erdos883Verified
