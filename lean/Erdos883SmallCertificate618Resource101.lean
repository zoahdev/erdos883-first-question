import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_101 :
    (List.ofFn coreChunks618_101).flatten =
      (coreData618.take (coreResources618 101).q).drop 258 := by
  decide +kernel

theorem coreCheck618_101 :
    ∀ c : Fin 1, (coreChunks618_101 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 101)) = true := by
  decide +kernel
#print axioms coreFlatten618_101
#print axioms coreCheck618_101
end Erdos883Verified
