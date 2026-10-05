import Erdos883AdaptiveSpan64924Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength64924_5 : adaptiveNumericSpans64924_5.length = 567 := by decide +kernel
theorem adaptiveSpanEvenCache64924_5 : adaptiveSpanEven64924_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain64924_5 : adaptiveSpanEven64924_5.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanEvenEntries64924_5 : adaptiveSpanEven64924_5.spans = coreEvenSpans 32462 0 adaptiveNumericSpans64924_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache64924_5 : adaptiveSpanWhole64924_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain64924_5 : adaptiveSpanWhole64924_5.domainCheck 32462 = true := by decide +kernel
theorem adaptiveSpanWholeEntries64924_5 : adaptiveSpanWhole64924_5.spans = coreWholeSpans 0 adaptiveNumericSpans64924_5 := by
  decide +kernel
end Erdos883Verified
