import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_35 :
    (List.ofFn coreChunks618_35).flatten =
      (coreData618.take (coreResources618 35).q).drop 152 := by
  decide +kernel

theorem coreCheck618_35 :
    ∀ c : Fin 1, (coreChunks618_35 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 35)) = true := by
  decide +kernel
#print axioms coreFlatten618_35
#print axioms coreCheck618_35
end Erdos883Verified
