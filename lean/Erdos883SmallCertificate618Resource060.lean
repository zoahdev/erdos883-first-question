import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_60 :
    (List.ofFn coreChunks618_60).flatten =
      (coreData618.take (coreResources618 60).q).drop 123 := by
  decide +kernel

theorem coreCheck618_60 :
    ∀ c : Fin 1, (coreChunks618_60 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 60)) = true := by
  decide +kernel
#print axioms coreFlatten618_60
#print axioms coreCheck618_60
end Erdos883Verified
