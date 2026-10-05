import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_7 :
    (List.ofFn coreChunks618_7).flatten =
      (coreData618.take (coreResources618 7).q).drop 83 := by
  decide +kernel

theorem coreCheck618_7 :
    ∀ c : Fin 2, (coreChunks618_7 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 7)) = true := by
  decide +kernel
#print axioms coreFlatten618_7
#print axioms coreCheck618_7
end Erdos883Verified
