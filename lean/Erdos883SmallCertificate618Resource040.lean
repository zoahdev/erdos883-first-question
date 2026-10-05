import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_40 :
    (List.ofFn coreChunks618_40).flatten =
      (coreData618.take (coreResources618 40).q).drop 90 := by
  decide +kernel

theorem coreCheck618_40 :
    ∀ c : Fin 1, (coreChunks618_40 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 40)) = true := by
  decide +kernel
#print axioms coreFlatten618_40
#print axioms coreCheck618_40
end Erdos883Verified
