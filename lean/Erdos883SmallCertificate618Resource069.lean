import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_69 :
    (List.ofFn coreChunks618_69).flatten =
      (coreData618.take (coreResources618 69).q).drop 137 := by
  decide +kernel

theorem coreCheck618_69 :
    ∀ c : Fin 1, (coreChunks618_69 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 69)) = true := by
  decide +kernel
#print axioms coreFlatten618_69
#print axioms coreCheck618_69
end Erdos883Verified
