import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_43 :
    (List.ofFn coreChunks618_43).flatten =
      (coreData618.take (coreResources618 43).q).drop 96 := by
  decide +kernel

theorem coreCheck618_43 :
    ∀ c : Fin 1, (coreChunks618_43 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 43)) = true := by
  decide +kernel
#print axioms coreFlatten618_43
#print axioms coreCheck618_43
end Erdos883Verified
