import Erdos883AdaptiveSpan64924Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength64924_3 : adaptiveNumericSpans64924_3.length = 567 := by decide +kernel
theorem adaptiveSpanEvenCache64924_3 : adaptiveSpanEven64924_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain64924_3 : adaptiveSpanEven64924_3.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanEvenEntries64924_3 : adaptiveSpanEven64924_3.spans = coreEvenSpans 32462 0 adaptiveNumericSpans64924_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache64924_3 : adaptiveSpanWhole64924_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain64924_3 : adaptiveSpanWhole64924_3.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanWholeEntries64924_3 : adaptiveSpanWhole64924_3.spans = coreWholeSpans 0 adaptiveNumericSpans64924_3 := by
  decide +kernel
end Erdos883Verified
