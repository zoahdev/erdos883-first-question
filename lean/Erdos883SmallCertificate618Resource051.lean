import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_51 :
    (List.ofFn coreChunks618_51).flatten =
      (coreData618.take (coreResources618 51).q).drop 105 := by
  decide +kernel

theorem coreCheck618_51 :
    ∀ c : Fin 1, (coreChunks618_51 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 51)) = true := by
  decide +kernel
#print axioms coreFlatten618_51
#print axioms coreCheck618_51
end Erdos883Verified
