import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_5 :
    (List.ofFn coreChunks618_5).flatten =
      (coreData618.take (coreResources618 5).q).drop 80 := by
  decide +kernel

theorem coreCheck618_5 :
    ∀ c : Fin 1, (coreChunks618_5 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 5)) = true := by
  decide +kernel
#print axioms coreFlatten618_5
#print axioms coreCheck618_5
end Erdos883Verified
