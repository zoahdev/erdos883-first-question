import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_71 :
    (List.ofFn coreChunks618_71).flatten =
      (coreData618.take (coreResources618 71).q).drop 139 := by
  decide +kernel

theorem coreCheck618_71 :
    ∀ c : Fin 1, (coreChunks618_71 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 71)) = true := by
  decide +kernel
#print axioms coreFlatten618_71
#print axioms coreCheck618_71
end Erdos883Verified
